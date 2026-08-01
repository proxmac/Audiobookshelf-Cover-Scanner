#!/usr/bin/env python3
"""
Audiobookshelf Cover Scanner (GUI)
===================================

A Windows-friendly desktop app that scans an audiobook library for cover
images below a minimum resolution (default 500x500) and lets you jump
straight to the item in Audiobookshelf's web UI.

Requirements (install once):
    pip install Pillow

Run:
    python cover_scanner_gui.py

--------------------------------------------------------------------------
TWO WAYS TO OPEN RESULTS IN AUDIOBOOKSHELF
--------------------------------------------------------------------------

1) "Metadata cache" mode (no server connection needed)
   If you point the scan at Audiobookshelf's internal cache folder
   (normally  <abs-data>/metadata/items/  ), each book's folder is
   already named with its Audiobookshelf item ID. Check the
   "Folder name = ABS item ID" box and results can be opened with a
   single click, no login required — it just builds:
       <server url>/item/<folder-name>

2) "Library" mode (scanning your actual audiobook folders)
   If you scan your real library (e.g. D:\\Audiobooks), folder names are
   book titles, not item IDs. Fill in your Audiobookshelf server URL and
   an API key (Settings > Users > (your user) > API Token in the ABS web
   UI), then click "Connect". The app downloads your library's item list
   once and matches each scanned folder to an item by folder/path name
   so it can open the right page.
--------------------------------------------------------------------------
"""

import csv
import json
import os
import queue
import subprocess
import threading
import urllib.error
import urllib.request
import webbrowser
from tkinter import (
    Tk, StringVar, IntVar, BooleanVar, filedialog, messagebox, ttk, END, W, E, N, S
)

try:
    from PIL import Image
except ImportError:
    Image = None

CONFIG_DIR = os.path.join(
    os.environ.get("APPDATA") or os.path.expanduser("~"),
    "AudiobookshelfCoverScanner",
)
CONFIG_PATH = os.path.join(CONFIG_DIR, "settings.json")

DEFAULT_COVER_NAMES = {
    "cover.jpg", "cover.jpeg", "cover.png", "cover.webp",
}
IMAGE_EXTENSIONS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp"}
AUDIO_EXTENSIONS = {".mp3", ".m4a", ".m4b", ".flac", ".ogg", ".opus", ".wav", ".aac"}
METADATA_FILENAMES = {"metadata.json"}


# --------------------------------------------------------------------------
# Scanning logic
# --------------------------------------------------------------------------

def is_excluded(path, excludes):
    """excludes entries can be a plain folder name (matches any folder with
    that name anywhere in the tree) or an absolute path (matches that
    folder and everything under it)."""
    if not excludes:
        return False
    norm = os.path.normpath(path)
    parts = norm.split(os.sep)
    for ex in excludes:
        ex_norm = os.path.normpath(ex.strip())
        if not ex_norm:
            continue
        if os.path.isabs(ex_norm):
            if norm == ex_norm or norm.startswith(ex_norm + os.sep):
                return True
        else:
            if any(part.lower() == ex_norm.lower() for part in parts):
                return True
    return False


def iter_scan_dirs(root, excludes=None):
    """Walk root, pruning excluded folders, yielding (dirpath, filenames)."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [
            d for d in dirnames if not is_excluded(os.path.join(dirpath, d), excludes)
        ]
        if is_excluded(dirpath, excludes):
            continue
        yield dirpath, filenames


def is_book_folder(filenames):
    """Heuristic: a folder is a 'book folder' if it has audio files or a
    recognized cover image in it (as opposed to a bare grouping folder)."""
    for fname in filenames:
        ext = os.path.splitext(fname)[1].lower()
        if ext in AUDIO_EXTENSIONS:
            return True
        if fname.lower() in DEFAULT_COVER_NAMES:
            return True
    return False


def has_metadata_json(filenames):
    return any(fname.lower() in METADATA_FILENAMES for fname in filenames)


def get_image_size(path):
    try:
        with Image.open(path) as img:
            return img.size, None
    except Exception as e:  # noqa: BLE001
        return None, str(e)


# --------------------------------------------------------------------------
# Audiobookshelf API helper
# --------------------------------------------------------------------------

class ABSClient:
    def __init__(self, base_url, api_key):
        self.base_url = base_url.rstrip("/")
        self.api_key = api_key.strip()

    def _get(self, path):
        req = urllib.request.Request(f"{self.base_url}{path}")
        if self.api_key:
            req.add_header("Authorization", f"Bearer {self.api_key}")
        with urllib.request.urlopen(req, timeout=15) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def list_libraries(self):
        data = self._get("/api/libraries")
        return data.get("libraries", [])

    def list_items(self, library_id):
        data = self._get(f"/api/libraries/{library_id}/items?limit=0")
        return data.get("results", [])

    def item_url(self, item_id):
        return f"{self.base_url}/item/{item_id}"


def best_match_item(folder_path, items):
    """Match a scanned book folder to an ABS library item by comparing
    the end of each item's on-disk path to the scanned folder path."""
    folder_norm = os.path.normpath(folder_path).replace("\\", "/").lower()
    folder_name = os.path.basename(folder_norm)

    # Pass 1: exact path suffix match
    for item in items:
        item_path = (item.get("path") or "").replace("\\", "/").lower()
        if item_path and (item_path == folder_norm or folder_norm.endswith(item_path) or item_path.endswith(folder_norm)):
            return item

    # Pass 2: match by final folder name only
    for item in items:
        item_path = (item.get("path") or "").replace("\\", "/").lower()
        if item_path and os.path.basename(item_path) == folder_name:
            return item

    # Pass 3: match by title
    for item in items:
        media = item.get("media", {}) or {}
        meta = media.get("metadata", {}) or {}
        title = (meta.get("title") or "").lower()
        if title and title == folder_name:
            return item

    return None


# --------------------------------------------------------------------------
# GUI
# --------------------------------------------------------------------------

class CoverScannerApp:
    def __init__(self, root):
        self.root = root
        root.title("Audiobookshelf Cover Scanner")
        root.geometry("1150x800")
        root.minsize(900, 560)

        self.msg_queue = queue.Queue()
        self.results = []          # list of dicts: path, folder, w, h, status, error, kind
        self.row_index = {}        # tree iid -> row dict
        self.abs_items = None      # cached list of items from ABS API
        self.abs_client = None

        self._build_widgets()
        self._pending_library_name = None
        self._load_settings()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.after(100, self._poll_queue)
        # Give the top settings pane a modest starting height so the
        # results table gets most of the window by default; the person
        # can still drag the sash to adjust this.
        self.root.after(50, lambda: self._paned.sashpos(0, 300))

    def _on_close(self):
        self._save_settings(silent=True)
        self.root.destroy()

    # ---- settings persistence ---------------------------------------------

    def _save_settings(self, silent=False):
        data = {
            "path": self.path_var.get(),
            "min_w": self.min_w_var.get(),
            "min_h": self.min_h_var.get(),
            "all_images": self.all_images_var.get(),
            "cache_mode": self.cache_mode_var.get(),
            "check_metadata": self.check_metadata_var.get(),
            "abs_url": self.abs_url_var.get(),
            "remember_key": self.remember_key_var.get(),
            "abs_key": self.abs_key_var.get() if self.remember_key_var.get() else "",
            "abs_library_name": self.abs_lib_var.get(),
            "excludes": self._get_excludes(),
            "dblclick_action": self.dblclick_action_var.get(),
            "file_manager": self.file_manager_var.get(),
            "custom_fm_path": self.custom_fm_path_var.get(),
        }
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            if not silent:
                messagebox.showinfo("Settings saved", f"Saved to:\n{CONFIG_PATH}")
        except Exception as e:  # noqa: BLE001
            if not silent:
                messagebox.showerror("Could not save settings", str(e))

    def _load_settings(self):
        if not os.path.isfile(CONFIG_PATH):
            return
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:  # noqa: BLE001
            return

        self.path_var.set(data.get("path", self.path_var.get()))
        self.min_w_var.set(data.get("min_w", self.min_w_var.get()))
        self.min_h_var.set(data.get("min_h", self.min_h_var.get()))
        self.all_images_var.set(data.get("all_images", self.all_images_var.get()))
        self.cache_mode_var.set(data.get("cache_mode", self.cache_mode_var.get()))
        self.check_metadata_var.set(data.get("check_metadata", self.check_metadata_var.get()))
        self.abs_url_var.set(data.get("abs_url", self.abs_url_var.get()))
        self.remember_key_var.set(data.get("remember_key", True))
        if self.remember_key_var.get():
            self.abs_key_var.set(data.get("abs_key", ""))
        self._pending_library_name = data.get("abs_library_name") or None
        self._set_excludes(data.get("excludes", []))

        self.dblclick_action_var.set(data.get("dblclick_action", "abs"))
        self._dblclick_combo.set(
            "Open in Audiobookshelf" if self.dblclick_action_var.get() == "abs" else "Open folder"
        )

        self.file_manager_var.set(data.get("file_manager", "explorer"))
        self.custom_fm_path_var.set(data.get("custom_fm_path", ""))
        self._fm_combo.set(
            "Custom application..." if self.file_manager_var.get() == "custom" else "Windows Explorer"
        )
        self._on_fm_choice_changed()

    # ---- UI construction --------------------------------------------------

    def _build_widgets(self):
        pad = {"padx": 6, "pady": 4}

        # Status bar lives outside the paned area, always visible at the bottom.
        self.status_var = StringVar(value="Ready.")
        ttk.Label(self.root, textvariable=self.status_var, anchor=W, relief="sunken").pack(fill="x", side="bottom")

        # Everything else sits in a vertical paned window so the person can
        # drag the divider to give the results table more (or less) room,
        # in addition to resizing the whole window.
        paned = ttk.PanedWindow(self.root, orient="vertical")
        paned.pack(fill="both", expand=True, padx=6, pady=6)
        self._paned = paned

        top_frame = ttk.Frame(paned)
        bottom_frame = ttk.Frame(paned)
        paned.add(top_frame, weight=0)
        paned.add(bottom_frame, weight=1)

        # --- Scan settings frame
        scan_frame = ttk.LabelFrame(top_frame, text="1. Scan settings")
        scan_frame.pack(fill="x")

        self.path_var = StringVar()
        ttk.Label(scan_frame, text="Library folder:").grid(row=0, column=0, sticky=W, **pad)
        ttk.Entry(scan_frame, textvariable=self.path_var, width=70).grid(row=0, column=1, sticky="we", **pad)
        ttk.Button(scan_frame, text="Browse...", command=self._browse_folder).grid(row=0, column=2, **pad)

        self.min_w_var = IntVar(value=500)
        self.min_h_var = IntVar(value=500)
        ttk.Label(scan_frame, text="Min width:").grid(row=1, column=0, sticky=W, **pad)
        ttk.Entry(scan_frame, textvariable=self.min_w_var, width=8).grid(row=1, column=1, sticky=W, **pad)
        ttk.Label(scan_frame, text="Min height:").grid(row=1, column=1, sticky=W, padx=(90, 6))
        ttk.Entry(scan_frame, textvariable=self.min_h_var, width=8).grid(row=1, column=1, sticky=W, padx=(170, 6))

        self.all_images_var = BooleanVar(value=False)
        ttk.Checkbutton(
            scan_frame, text="Check every image file (not just cover.jpg/png/etc.)",
            variable=self.all_images_var
        ).grid(row=2, column=1, sticky=W, **pad)

        self.cache_mode_var = BooleanVar(value=False)
        ttk.Checkbutton(
            scan_frame, text="Folder name = ABS item ID (scanning ABS metadata cache)",
            variable=self.cache_mode_var
        ).grid(row=3, column=1, sticky=W, **pad)

        self.check_metadata_var = BooleanVar(value=True)
        ttk.Checkbutton(
            scan_frame, text="Also flag book folders missing metadata.json",
            variable=self.check_metadata_var
        ).grid(row=3, column=2, sticky=W, **pad)

        # --- Excluded folders
        ttk.Label(scan_frame, text="Exclude folders:").grid(row=4, column=0, sticky="nw", **pad)
        exclude_container = ttk.Frame(scan_frame)
        exclude_container.grid(row=4, column=1, columnspan=2, sticky="we", **pad)

        self.exclude_listbox = ttk.Treeview(
            exclude_container, columns=("value",), show="headings", height=4, selectmode="extended"
        )
        self.exclude_listbox.heading("value", text="Excluded folder names / paths")
        self.exclude_listbox.column("value", width=520)
        self.exclude_listbox.pack(side="left", fill="x", expand=True)

        exclude_btns = ttk.Frame(exclude_container)
        exclude_btns.pack(side="left", padx=(6, 0))
        ttk.Button(exclude_btns, text="Add folder...", command=self._add_exclude_browse).pack(fill="x", pady=2)
        ttk.Button(exclude_btns, text="Add name...", command=self._add_exclude_name).pack(fill="x", pady=2)
        ttk.Button(exclude_btns, text="Remove selected", command=self._remove_selected_excludes).pack(fill="x", pady=2)

        self.scan_btn = ttk.Button(scan_frame, text="Scan", command=self._start_scan)
        self.scan_btn.grid(row=5, column=1, sticky=W, **pad)

        scan_frame.columnconfigure(1, weight=1)

        # --- Audiobookshelf connection frame
        abs_frame = ttk.LabelFrame(top_frame, text="2. Audiobookshelf connection (for 'Library' mode)")
        abs_frame.pack(fill="x", pady=(6, 0))

        self.abs_url_var = StringVar(value="http://localhost:13378")
        self.abs_key_var = StringVar()
        self.abs_lib_var = StringVar()

        ttk.Label(abs_frame, text="Server URL:").grid(row=0, column=0, sticky=W, **pad)
        ttk.Entry(abs_frame, textvariable=self.abs_url_var, width=40).grid(row=0, column=1, sticky=W, **pad)

        ttk.Label(abs_frame, text="API key:").grid(row=0, column=2, sticky=W, **pad)
        ttk.Entry(abs_frame, textvariable=self.abs_key_var, width=30, show="*").grid(row=0, column=3, sticky=W, **pad)

        ttk.Label(abs_frame, text="Library:").grid(row=1, column=0, sticky=W, **pad)
        self.lib_combo = ttk.Combobox(abs_frame, textvariable=self.abs_lib_var, width=37, state="readonly")
        self.lib_combo.grid(row=1, column=1, sticky=W, **pad)

        ttk.Button(abs_frame, text="Connect / Refresh libraries", command=self._connect_abs).grid(row=1, column=2, **pad)
        self.abs_status_var = StringVar(value="Not connected")
        ttk.Label(abs_frame, textvariable=self.abs_status_var, foreground="gray").grid(row=1, column=3, sticky=W, **pad)

        self.remember_key_var = BooleanVar(value=True)
        ttk.Checkbutton(
            abs_frame, text="Remember API key on this computer (saved in plain text)",
            variable=self.remember_key_var
        ).grid(row=2, column=1, columnspan=2, sticky=W, **pad)

        ttk.Button(abs_frame, text="Save settings", command=self._save_settings).grid(row=2, column=3, sticky=W, **pad)

        # --- Preferences frame (double-click action + file manager)
        prefs_frame = ttk.LabelFrame(top_frame, text="3. Preferences")
        prefs_frame.pack(fill="x", pady=(6, 0))

        self.dblclick_action_var = StringVar(value="abs")
        ttk.Label(prefs_frame, text="Double-click a result to:").grid(row=0, column=0, sticky=W, **pad)
        dblclick_combo = ttk.Combobox(
            prefs_frame, state="readonly", width=24,
            values=["Open in Audiobookshelf", "Open folder"],
        )
        dblclick_combo.current(0)
        dblclick_combo.grid(row=0, column=1, sticky=W, **pad)
        dblclick_combo.bind("<<ComboboxSelected>>", lambda e: self.dblclick_action_var.set(
            "abs" if dblclick_combo.get() == "Open in Audiobookshelf" else "folder"
        ))
        self._dblclick_combo = dblclick_combo

        self.file_manager_var = StringVar(value="explorer")
        ttk.Label(prefs_frame, text="Open folder with:").grid(row=0, column=2, sticky=W, **pad)
        fm_combo = ttk.Combobox(
            prefs_frame, state="readonly", width=20,
            values=["Windows Explorer", "Custom application..."],
        )
        fm_combo.current(0)
        fm_combo.grid(row=0, column=3, sticky=W, **pad)
        self._fm_combo = fm_combo

        self.custom_fm_path_var = StringVar()
        self.custom_fm_entry = ttk.Entry(prefs_frame, textvariable=self.custom_fm_path_var, width=40, state="disabled")
        self.custom_fm_entry.grid(row=1, column=2, columnspan=1, sticky="we", **pad)
        self.custom_fm_browse_btn = ttk.Button(
            prefs_frame, text="Browse...", command=self._browse_custom_fm, state="disabled"
        )
        self.custom_fm_browse_btn.grid(row=1, column=3, sticky=W, **pad)

        fm_combo.bind("<<ComboboxSelected>>", lambda e: self._on_fm_choice_changed())

        # --- Results frame
        results_frame = ttk.LabelFrame(bottom_frame, text="4. Results")
        results_frame.pack(fill="both", expand=True)

        columns = ("folder", "resolution", "status", "path")
        self.tree = ttk.Treeview(results_frame, columns=columns, show="headings", selectmode="browse")
        self._sort_state = {}  # column -> last sort was reverse (bool)
        headings = {"folder": "Book folder", "resolution": "Resolution", "status": "Status", "path": "File"}
        for col, text in headings.items():
            self.tree.heading(col, text=text, command=lambda c=col: self._sort_by_column(c))
        self.tree.column("folder", width=220)
        self.tree.column("resolution", width=100, anchor="center")
        self.tree.column("status", width=100, anchor="center")
        self.tree.column("path", width=480)
        self.tree.pack(fill="both", expand=True, side="left", padx=(6, 0), pady=6)
        self.tree.bind("<Double-1>", self._on_row_double_click)

        scrollbar = ttk.Scrollbar(results_frame, orient="vertical", command=self.tree.yview)
        scrollbar.pack(side="left", fill="y")
        self.tree.configure(yscrollcommand=scrollbar.set)

        # --- Action buttons
        action_frame = ttk.Frame(bottom_frame)
        action_frame.pack(fill="x", pady=(6, 0))

        ttk.Button(action_frame, text="Open in Audiobookshelf", command=self._open_selected_in_abs).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Open folder", command=self._open_selected_folder).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Export CSV...", command=self._export_csv).pack(side="left", padx=4)

    # ---- exclude folder management ----------------------------------------

    def _add_exclude_browse(self):
        folder = filedialog.askdirectory(title="Choose a folder to exclude")
        if folder:
            self._add_exclude_value(os.path.normpath(folder))

    def _add_exclude_name(self):
        from tkinter.simpledialog import askstring
        name = askstring(
            "Exclude by name",
            "Folder name to exclude (matches anywhere in the library, e.g. 'Podcasts'):"
        )
        if name and name.strip():
            self._add_exclude_value(name.strip())

    def _add_exclude_value(self, value):
        existing = {self.exclude_listbox.item(i, "values")[0] for i in self.exclude_listbox.get_children()}
        if value not in existing:
            self.exclude_listbox.insert("", END, values=(value,))

    def _remove_selected_excludes(self):
        for item in self.exclude_listbox.selection():
            self.exclude_listbox.delete(item)

    def _get_excludes(self):
        return [self.exclude_listbox.item(i, "values")[0] for i in self.exclude_listbox.get_children()]

    def _set_excludes(self, values):
        for item in self.exclude_listbox.get_children():
            self.exclude_listbox.delete(item)
        for value in values or []:
            self.exclude_listbox.insert("", END, values=(value,))

    # ---- helpers ------------------------------------------------------

    def _browse_folder(self):
        folder = filedialog.askdirectory()
        if folder:
            self.path_var.set(folder)

    def _on_fm_choice_changed(self):
        is_custom = self._fm_combo.get() == "Custom application..."
        self.file_manager_var.set("custom" if is_custom else "explorer")
        state = "normal" if is_custom else "disabled"
        self.custom_fm_entry.config(state=state)
        self.custom_fm_browse_btn.config(state=state)

    def _browse_custom_fm(self):
        path = filedialog.askopenfilename(
            title="Choose file manager executable",
            filetypes=[("Executable", "*.exe"), ("All files", "*.*")],
        )
        if path:
            self.custom_fm_path_var.set(path)

    def _on_row_double_click(self, event):
        item = self.tree.identify_row(event.y)
        if not item:
            return
        self.tree.selection_set(item)
        if self.dblclick_action_var.get() == "abs":
            self._open_selected_in_abs()
        else:
            self._open_selected_folder()

    def _poll_queue(self):
        try:
            while True:
                kind, payload = self.msg_queue.get_nowait()
                if kind == "status":
                    self.status_var.set(payload)
                elif kind == "row":
                    self._insert_row(payload)
                elif kind == "scan_done":
                    self.scan_btn.config(state="normal")
                    self.status_var.set(payload)
                elif kind == "libraries":
                    self._populate_libraries(payload)
                elif kind == "error":
                    messagebox.showerror("Error", payload)
        except queue.Empty:
            pass
        self.root.after(100, self._poll_queue)

    def _insert_row(self, row):
        self.results.append(row)
        if row["status"] == "TOO SMALL":
            tag = "small"
        elif row["status"] == "ERROR":
            tag = "err"
        elif row["status"] == "MISSING METADATA":
            tag = "meta"
        else:
            tag = "ok"
        resolution = f'{row["w"]}x{row["h"]}' if row["w"] else "-"
        iid = self.tree.insert(
            "", END,
            values=(row["folder"], resolution, row["status"], row["path"]),
            tags=(tag,)
        )
        self.row_index[iid] = row
        self.tree.tag_configure("small", foreground="#b00020")
        self.tree.tag_configure("err", foreground="#888888")
        self.tree.tag_configure("ok", foreground="#1a7f37")
        self.tree.tag_configure("meta", foreground="#a15c00")

    # ---- sorting ----------------------------------------------------------

    def _sort_by_column(self, col):
        reverse = self._sort_state.get(col, False)
        rows = [(self.tree.set(item, col), item) for item in self.tree.get_children("")]

        if col == "resolution":
            def key(pair):
                text = pair[0]
                if text == "-" or "x" not in text:
                    return (-1, -1)
                w_str, h_str = text.split("x", 1)
                try:
                    return (int(w_str), int(h_str))
                except ValueError:
                    return (-1, -1)
        else:
            def key(pair):
                return pair[0].lower()

        rows.sort(key=key, reverse=reverse)
        for index, (_value, item) in enumerate(rows):
            self.tree.move(item, "", index)

        # Update heading arrows and flip direction for next click
        for c in ("folder", "resolution", "status", "path"):
            base_text = {"folder": "Book folder", "resolution": "Resolution",
                         "status": "Status", "path": "File"}[c]
            if c == col:
                arrow = " \u25bc" if reverse else " \u25b2"
                self.tree.heading(c, text=base_text + arrow)
            else:
                self.tree.heading(c, text=base_text)
        self._sort_state[col] = not reverse

    # ---- scanning -------------------------------------------------------

    def _start_scan(self):
        if Image is None:
            messagebox.showerror(
                "Pillow not installed",
                "This tool needs Pillow. Install it with:\n\n    pip install Pillow"
            )
            return

        root_path = self.path_var.get().strip()
        if not root_path or not os.path.isdir(root_path):
            messagebox.showerror("Invalid folder", "Please choose a valid library folder.")
            return

        for item in self.tree.get_children():
            self.tree.delete(item)
        self.results.clear()
        self.row_index.clear()

        self.scan_btn.config(state="disabled")
        self.status_var.set("Scanning...")

        min_w = self.min_w_var.get()
        min_h = self.min_h_var.get()
        all_images = self.all_images_var.get()
        check_metadata = self.check_metadata_var.get()
        excludes = self._get_excludes()

        thread = threading.Thread(
            target=self._scan_worker,
            args=(root_path, min_w, min_h, all_images, excludes, check_metadata),
            daemon=True,
        )
        thread.start()

    def _scan_worker(self, root_path, min_w, min_h, all_images, excludes, check_metadata):
        checked = 0
        small = 0
        errors = 0
        missing_meta = 0

        for dirpath, filenames in iter_scan_dirs(root_path, excludes):
            folder = os.path.basename(dirpath)

            # --- cover resolution checks
            for fname in filenames:
                ext = os.path.splitext(fname)[1].lower()
                if ext not in IMAGE_EXTENSIONS:
                    continue
                if not (all_images or fname.lower() in DEFAULT_COVER_NAMES):
                    continue

                filepath = os.path.join(dirpath, fname)
                checked += 1
                size, err = get_image_size(filepath)
                if size is None:
                    errors += 1
                    self.msg_queue.put(("row", {
                        "path": filepath, "folder": folder, "w": None, "h": None,
                        "status": "ERROR", "error": err, "kind": "cover"
                    }))
                    continue
                w, h = size
                ok = w >= min_w and h >= min_h
                if not ok:
                    small += 1
                status = "OK" if ok else "TOO SMALL"
                self.msg_queue.put(("row", {
                    "path": filepath, "folder": folder, "w": w, "h": h,
                    "status": status, "error": None, "kind": "cover"
                }))

            # --- missing metadata.json check
            if check_metadata and is_book_folder(filenames) and not has_metadata_json(filenames):
                missing_meta += 1
                self.msg_queue.put(("row", {
                    "path": dirpath, "folder": folder, "w": None, "h": None,
                    "status": "MISSING METADATA", "error": None, "kind": "metadata"
                }))

            self.msg_queue.put((
                "status",
                f"Scanning... checked {checked} cover(s), {small} too small, "
                f"{missing_meta} missing metadata.json"
            ))

        self.msg_queue.put((
            "scan_done",
            f"Done. Checked {checked} cover(s): {small} below threshold, {errors} error(s). "
            f"{missing_meta} folder(s) missing metadata.json."
        ))

    # ---- Audiobookshelf connection ---------------------------------------

    def _connect_abs(self):
        url = self.abs_url_var.get().strip()
        key = self.abs_key_var.get().strip()
        if not url:
            messagebox.showerror("Missing URL", "Enter your Audiobookshelf server URL.")
            return
        self.abs_status_var.set("Connecting...")
        thread = threading.Thread(target=self._connect_abs_worker, args=(url, key), daemon=True)
        thread.start()

    def _connect_abs_worker(self, url, key):
        try:
            client = ABSClient(url, key)
            libraries = client.list_libraries()
            self.abs_client = client
            self.msg_queue.put(("libraries", libraries))
        except urllib.error.HTTPError as e:
            self.msg_queue.put(("error", f"Audiobookshelf returned an error: {e.code} {e.reason}"))
            self.msg_queue.put(("status", "Connection failed."))
        except Exception as e:  # noqa: BLE001
            self.msg_queue.put(("error", f"Could not connect to Audiobookshelf:\n{e}"))
            self.msg_queue.put(("status", "Connection failed."))

    def _populate_libraries(self, libraries):
        self._libraries = libraries
        names = [lib.get("name", lib.get("id")) for lib in libraries]
        self.lib_combo["values"] = names
        if names:
            if self._pending_library_name in names:
                self.lib_combo.set(self._pending_library_name)
            else:
                self.lib_combo.current(0)
        self._pending_library_name = None
        self.abs_status_var.set(f"Connected. {len(libraries)} librar{'y' if len(libraries) == 1 else 'ies'} found.")
        self.abs_items = None  # reset cache, will fetch on first "open"

    def _current_library_id(self):
        if not getattr(self, "_libraries", None):
            return None
        idx = self.lib_combo.current()
        if idx < 0:
            return None
        return self._libraries[idx].get("id")

    # ---- open in ABS / explorer ------------------------------------------

    def _selected_row(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("No selection", "Select a result row first.")
            return None
        row = self.row_index.get(sel[0])
        if row is None:
            return None
        return row

    @staticmethod
    def _book_folder_for(row):
        """The on-disk book folder for a row, whether it's a cover file
        (folder = its parent) or a missing-metadata row (path IS the folder)."""
        if row.get("kind") == "metadata":
            return row["path"]
        return os.path.dirname(row["path"])

    def _open_selected_in_abs(self):
        row = self._selected_row()
        if not row:
            return

        base_url = self.abs_url_var.get().strip().rstrip("/")
        if not base_url:
            messagebox.showerror("Missing URL", "Enter your Audiobookshelf server URL.")
            return

        book_folder = self._book_folder_for(row)

        if self.cache_mode_var.get():
            item_id = row["folder"]
            webbrowser.open(f"{base_url}/item/{item_id}")
            return

        if self.abs_client is None:
            messagebox.showinfo(
                "Not connected",
                "Click 'Connect / Refresh libraries' first, or enable "
                "'Folder name = ABS item ID' if you scanned the metadata cache."
            )
            return

        lib_id = self._current_library_id()
        if not lib_id:
            messagebox.showinfo("No library selected", "Pick a library from the dropdown first.")
            return

        self.status_var.set("Looking up item in Audiobookshelf...")
        thread = threading.Thread(target=self._open_in_abs_worker, args=(lib_id, book_folder, base_url), daemon=True)
        thread.start()

    def _open_in_abs_worker(self, lib_id, book_folder, base_url):
        try:
            if self.abs_items is None:
                self.abs_items = self.abs_client.list_items(lib_id)
            match = best_match_item(book_folder, self.abs_items)
            if match is None:
                self.msg_queue.put(("error", "Couldn't find a matching item in this library. Try a different library, or check the folder is inside your ABS library path."))
                self.msg_queue.put(("status", "No match found."))
                return
            url = self.abs_client.item_url(match["id"])
            webbrowser.open(url)
            self.msg_queue.put(("status", f"Opened: {url}"))
        except Exception as e:  # noqa: BLE001
            self.msg_queue.put(("error", f"Lookup failed:\n{e}"))
            self.msg_queue.put(("status", "Lookup failed."))

    def _open_selected_folder(self):
        row = self._selected_row()
        if not row:
            return
        folder = self._book_folder_for(row)

        if self.file_manager_var.get() == "custom":
            exe = self.custom_fm_path_var.get().strip()
            if not exe:
                messagebox.showerror(
                    "No file manager set",
                    "Choose a custom file manager executable in Preferences, "
                    "or switch back to Windows Explorer."
                )
                return
            try:
                subprocess.Popen([exe, folder])
            except Exception as e:  # noqa: BLE001
                messagebox.showerror("Could not launch file manager", str(e))
            return

        try:
            os.startfile(folder)  # Windows only
        except AttributeError:
            messagebox.showinfo("Unsupported", "Folder opening is only wired up for Windows in this build.")
        except Exception as e:  # noqa: BLE001
            messagebox.showerror("Could not open folder", str(e))

    # ---- export -----------------------------------------------------------

    def _export_csv(self):
        if not self.results:
            messagebox.showinfo("Nothing to export", "Run a scan first.")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files", "*.csv")])
        if not path:
            return
        with open(path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["kind", "folder", "path", "width", "height", "status", "error"])
            for r in self.results:
                writer.writerow([r.get("kind", ""), r["folder"], r["path"], r["w"] or "", r["h"] or "", r["status"], r["error"] or ""])
        messagebox.showinfo("Exported", f"Results saved to:\n{path}")


def main():
    root = Tk()
    try:
        ttk.Style().theme_use("vista")
    except Exception:
        pass
    CoverScannerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
