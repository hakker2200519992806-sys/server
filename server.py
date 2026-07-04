"""
╔══════════════════════════════════════════════════════════════════════════════╗
║         🖥  UNIVERSAL SERVER BOSHQARUV TIZIMI  —  server.py  (v2.1)         ║
║         Python + Flask + SQLite  |  Windows uchun (o'rnatish shart emas)   ║
╠══════════════════════════════════════════════════════════════════════════════╣
║  Majburiy o'rnatish:                                                        ║
║    pip install flask                                                        ║
║                                                                             ║
║  Ixtiyoriy (qo'shimcha funksiyalar uchun):                                  ║
║    pip install pyngrok colorama psutil qrcode[pil]                          ║
║      - pyngrok  -> Global rejim (internet orqali havola)                    ║
║      - colorama -> Terminalda rangli chiqish                                ║
║      - psutil   -> Server monitoring (CPU/RAM/Disk)                         ║
║      - qrcode   -> Havolalar uchun QR-kod                                   ║
║                                                                             ║
║  SQLite — alohida o'rnatish shart emas, Python bilan birga keladi!         ║
║  Ma'lumotlar: server_data.db faylida saqlanadi                              ║
║  Ishlatish: python server.py                                                ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

import os, sys, re, json, time, uuid, socket, secrets, hashlib, threading
import subprocess, platform, sqlite3, io, shutil, zipfile, traceback
import urllib.request, urllib.parse
import multiprocessing as mp
from datetime import datetime, timedelta
from functools import wraps
from pathlib import Path
from contextlib import contextmanager

# ── Uchinchi tomon ─────────────────────────────────────────────────────────
try:
    from flask import (Flask, request, jsonify, session, redirect,
                       send_from_directory, send_file, Response, abort)
    from werkzeug.utils import secure_filename
    from werkzeug.security import generate_password_hash, check_password_hash
except ImportError:
    sys.exit("pip install flask")

try:
    from pyngrok import ngrok as _ngrok
    NGROK_OK = True
except ImportError:
    NGROK_OK = False

try:
    from colorama import Fore, Style, init as _cinit
    _cinit(autoreset=True)
    R=Fore.RED; G=Fore.GREEN; Y=Fore.YELLOW; C=Fore.CYAN; M=Fore.MAGENTA; W=Fore.WHITE
    def _c(t, col=""): return col + Style.BRIGHT + str(t) + Style.RESET_ALL
except ImportError:
    R=G=Y=C=M=W=""
    def _c(t, col=""): return str(t)

try:
    import psutil
    PSUTIL_OK = True
except ImportError:
    PSUTIL_OK = False

try:
    import qrcode
    QRCODE_OK = True
except ImportError:
    QRCODE_OK = False

# ── RestrictedPython — ixtiyoriy bog'liqlik (backend uchun) ────────────────
try:
    from RestrictedPython import compile_restricted, safe_globals
    from RestrictedPython.Guards import (
        safe_builtins, guarded_iter_unpack_sequence, full_write_guard,
    )
    from RestrictedPython.Eval import default_guarded_getiter
    RESTRICTED_OK = True
except ImportError:
    RESTRICTED_OK = False

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                 BACKEND ENGINE SOZLAMALARI                               ║
# ╚══════════════════════════════════════════════════════════════════════════╝
EXEC_TIMEOUT_SEC   = 3          # bir chaqiruv uchun maksimal ijro vaqti
MEM_LIMIT_MB       = 128        # protsess uchun taxminiy xotira chegarasi (Linux)
RATE_LIMIT_PER_MIN = 30         # foydalanuvchi/loyiha uchun daqiqasiga chaqiruv
HISTORY_LOG_KEEP   = 500        # backend_exec_logs jadvalida saqlanadigan maksimal yozuv

PROJECT_DB_DIR = Path("project_dbs")
PROJECT_DB_DIR.mkdir(exist_ok=True)

# Foydalanuvchi kodi ichida "import X" ga ruxsat etilgan modullar
ALLOWED_IMPORTS = {"json", "math", "random", "re", "datetime", "string", "statistics"}

# SQL darajasida taqiqlangan kalit so'zlar
_SQL_FORBIDDEN = re.compile(
    r"\b(ATTACH|DETACH|PRAGMA|VACUUM|DROP\s+DATABASE|LOAD_EXTENSION)\b", re.I)

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                          KONFIGURATSIYA                                  ║
# ╚══════════════════════════════════════════════════════════════════════════╝
CFG = {
    "DB_FILE":        "server_data.db",   # SQLite fayl nomi
    "PORT":           5000,
    "SECRET":         secrets.token_hex(32),
    "ADMIN_USER":     "admin",
    "ADMIN_PASS":     "Admin123!",
    "NGROK_TOKEN":    "",                 # https://dashboard.ngrok.com
    "TELEGRAM_TOKEN": "",                 # BotFather orqali olingan bot token
    "TELEGRAM_CHAT_ID": "",               # @userinfobot orqali olingan chat id
    "UPLOAD_DIR":     "uploads",
    "MAX_FILE_MB":    50,
    "ALLOWED_EXT":    {".html",".css",".js",".txt",".json",".png",".jpg",
                       ".jpeg",".gif",".svg",".ico",".woff",".woff2",".ttf",
                       ".mp3",".mp4",".py",".php"},
    "MAX_LOGIN_FAIL": 5,
    "BAN_MINUTES":    30,
    "SESSION_HOURS":  8,
}

UPLOAD_PATH   = Path(CFG["UPLOAD_DIR"])
FILES_PATH    = UPLOAD_PATH / "files"
for _p in [UPLOAD_PATH, FILES_PATH]:
    _p.mkdir(exist_ok=True)

app = Flask(__name__)
app.secret_key = CFG["SECRET"]
app.permanent_session_lifetime = timedelta(hours=CFG["SESSION_HOURS"])

_active_mode  = {"mode": None, "url": None}
_ngrok_tunnel = None
_db_lock      = threading.Lock()
PROCESS_START = time.time()

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                          DATABASE — SQLite                               ║
# ╚══════════════════════════════════════════════════════════════════════════╝
def get_conn():
    conn = sqlite3.connect(CFG["DB_FILE"], check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA foreign_keys=ON")
    return conn

def db_exec(sql, args=None, fetch=True):
    with _db_lock:
        conn = get_conn()
        try:
            cur = conn.execute(sql, args or ())
            if fetch:
                rows = cur.fetchall()
                return [dict(r) for r in rows]
            conn.commit()
            return cur.lastrowid or True
        except Exception as e:
            print(_c(f"[SQL] {e}", R))
            return ([] if fetch else False)
        finally:
            conn.close()

def q1(sql, args=None):
    r = db_exec(sql, args)
    return r[0] if r else None

def setup_db():
    stmts = [
        """CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            email TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            role TEXT DEFAULT 'user',
            is_active INTEGER DEFAULT 1,
            bandwidth_limit_mb INTEGER DEFAULT 0,
            bandwidth_used_mb REAL DEFAULT 0,
            created_at TEXT DEFAULT (datetime('now')),
            last_login TEXT)""",

        """CREATE TABLE IF NOT EXISTS links (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            token TEXT UNIQUE NOT NULL,
            mode TEXT NOT NULL,
            label TEXT,
            target_path TEXT,
            password_hash TEXT,
            expires_at TEXT,
            is_active INTEGER DEFAULT 1,
            owner_id INTEGER,
            project_id INTEGER,
            visit_count INTEGER DEFAULT 0,
            created_at TEXT DEFAULT (datetime('now')))""",

        """CREATE TABLE IF NOT EXISTS access_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            link_token TEXT,
            mode TEXT,
            ip_address TEXT,
            user_agent TEXT,
            referer TEXT,
            bytes_served INTEGER DEFAULT 0,
            status_code INTEGER DEFAULT 200,
            path TEXT,
            visited_at TEXT DEFAULT (datetime('now')))""",

        """CREATE TABLE IF NOT EXISTS failed_logins (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ip_address TEXT NOT NULL,
            username TEXT,
            attempt_at TEXT DEFAULT (datetime('now')))""",

        """CREATE TABLE IF NOT EXISTS blocked_ips (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ip_address TEXT UNIQUE NOT NULL,
            reason TEXT,
            blocked_at TEXT DEFAULT (datetime('now')),
            unblock_at TEXT)""",

        """CREATE TABLE IF NOT EXISTS files (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            uuid TEXT UNIQUE NOT NULL,
            original_name TEXT NOT NULL,
            stored_name TEXT NOT NULL,
            file_type TEXT,
            file_size_bytes INTEGER DEFAULT 0,
            owner_id INTEGER,
            is_public INTEGER DEFAULT 0,
            download_count INTEGER DEFAULT 0,
            expires_at TEXT,
            created_at TEXT DEFAULT (datetime('now')))""",

        """CREATE TABLE IF NOT EXISTS projects (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            uuid TEXT UNIQUE NOT NULL,
            name TEXT NOT NULL,
            owner_id INTEGER,
            current_version INTEGER DEFAULT 1,
            is_public INTEGER DEFAULT 0,
            share_token TEXT,
            created_at TEXT DEFAULT (datetime('now')),
            updated_at TEXT DEFAULT (datetime('now')))""",

        """CREATE TABLE IF NOT EXISTS project_versions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            version INTEGER NOT NULL,
            html_code TEXT,
            css_code TEXT,
            js_code TEXT,
            notes TEXT,
            created_at TEXT DEFAULT (datetime('now')),
            UNIQUE(project_id, version))""",

        """CREATE TABLE IF NOT EXISTS mode_settings (
            mode TEXT PRIMARY KEY,
            is_enabled INTEGER DEFAULT 1)""",

        """CREATE TABLE IF NOT EXISTS bandwidth_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ip_address TEXT,
            bytes_used INTEGER DEFAULT 0,
            log_date TEXT DEFAULT (date('now')))""",

        # Sozlamalarni key-value ko'rinishida saqlash (Telegram, sayt nomi, server holati va h.k.)
        """CREATE TABLE IF NOT EXISTS app_settings (
            key TEXT PRIMARY KEY,
            value TEXT)""",

        # Ko'p fayl/papkali loyihalar uchun virtual fayl tizimi
        """CREATE TABLE IF NOT EXISTS project_files (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            path TEXT NOT NULL,
            is_folder INTEGER DEFAULT 0,
            content TEXT,
            created_at TEXT DEFAULT (datetime('now')),
            updated_at TEXT DEFAULT (datetime('now')),
            UNIQUE(project_id, path))""",

        # Har bir saqlashda oldingi tarkib tarixi (versiya tarixi / restore uchun)
        """CREATE TABLE IF NOT EXISTS project_file_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            path TEXT NOT NULL,
            content TEXT,
            saved_at TEXT DEFAULT (datetime('now')))""",

        # Foydalanuvchi shaxsiy Emmet/kod bo'laklari (snippets)
        """CREATE TABLE IF NOT EXISTS user_snippets (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            lang TEXT NOT NULL,
            trigger_key TEXT NOT NULL,
            body TEXT NOT NULL,
            created_at TEXT DEFAULT (datetime('now')))""",

        # API kalitlari (Bearer token orqali tashqi integratsiyalar uchun)
        """CREATE TABLE IF NOT EXISTS api_keys (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            name TEXT,
            key_prefix TEXT,
            key_hash TEXT NOT NULL,
            created_at TEXT DEFAULT (datetime('now')),
            last_used_at TEXT,
            revoked INTEGER DEFAULT 0)""",

        # 2FA (Telegram orqali bir martalik kod) uchun vaqtinchalik kodlar
        """CREATE TABLE IF NOT EXISTS two_fa_codes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            code TEXT NOT NULL,
            expires_at TEXT NOT NULL,
            used INTEGER DEFAULT 0,
            created_at TEXT DEFAULT (datetime('now')))""",

        # ═══════════════ YANGI FUNKSIYALAR UCHUN JADVALLAR ═══════════════

        # Jamoa/Team tizimi
        """CREATE TABLE IF NOT EXISTS project_teams (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            role TEXT DEFAULT 'viewer',
            invited_by INTEGER,
            created_at TEXT DEFAULT (datetime('now')),
            UNIQUE(project_id, user_id))""",

        # Audit trail — barcha o'zgarishlar logi
        """CREATE TABLE IF NOT EXISTS audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            username TEXT,
            action TEXT NOT NULL,
            target_type TEXT,
            target_id TEXT,
            details TEXT,
            ip_address TEXT,
            created_at TEXT DEFAULT (datetime('now')))""",

        # Real-time Chat xabarlari
        """CREATE TABLE IF NOT EXISTS chat_messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            username TEXT,
            message TEXT NOT NULL,
            created_at TEXT DEFAULT (datetime('now')))""",

        # TODO/Vazifalar ro'yxati
        """CREATE TABLE IF NOT EXISTS project_todos (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            is_done INTEGER DEFAULT 0,
            priority TEXT DEFAULT 'normal',
            created_at TEXT DEFAULT (datetime('now')),
            completed_at TEXT)""",

        # IP Whitelist
        """CREATE TABLE IF NOT EXISTS ip_whitelist (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ip_address TEXT NOT NULL UNIQUE,
            label TEXT,
            added_by INTEGER,
            created_at TEXT DEFAULT (datetime('now')))""",

        # Custom domain/subdomain
        """CREATE TABLE IF NOT EXISTS custom_domains (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            domain TEXT NOT NULL UNIQUE,
            is_active INTEGER DEFAULT 1,
            created_by INTEGER,
            created_at TEXT DEFAULT (datetime('now')))""",

        # Uptime monitoring logs
        """CREATE TABLE IF NOT EXISTS uptime_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            status TEXT DEFAULT 'up',
            response_ms INTEGER,
            checked_at TEXT DEFAULT (datetime('now')))""",
    ]
    _setup_backend_tables()
    for s in stmts:
        db_exec(s, fetch=False)

    for mode in ("private", "lan", "global"):
        db_exec("INSERT OR IGNORE INTO mode_settings (mode,is_enabled) VALUES (?,1)", (mode,), fetch=False)

    _ensure_column("users", "tg_chat_id", "TEXT")
    _ensure_column("users", "require_2fa", "INTEGER DEFAULT 0")

    if not q1("SELECT id FROM users WHERE role='admin' LIMIT 1"):
        ph = generate_password_hash(CFG["ADMIN_PASS"])
        db_exec("INSERT OR IGNORE INTO users (username,email,password_hash,role) VALUES (?,?,?,'admin')",
                (CFG["ADMIN_USER"], f"{CFG['ADMIN_USER']}@local.dev", ph), fetch=False)

    print(_c("  ✓ SQLite jadvallar tayyor", G))

def _ensure_column(table, col, coldef):
    """CREATE TABLE IF NOT EXISTS ustun qo'shmaydi — shu funksiya eski bazaga xavfsiz ustun qo'shadi."""
    cols = [r["name"] for r in db_exec(f"PRAGMA table_info({table})")]
    if col not in cols:
        db_exec(f"ALTER TABLE {table} ADD COLUMN {col} {coldef}", fetch=False)

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                      YORDAMCHI FUNKSIYALAR                               ║
# ╚══════════════════════════════════════════════════════════════════════════╝
def get_ip():
    return (request.headers.get("X-Forwarded-For","").split(",")[0].strip()
            or request.remote_addr or "unknown")

def log_access(mode, token=None, status=200, path=None, nb=0):
    db_exec(
        "INSERT INTO access_logs (link_token,mode,ip_address,user_agent,referer,bytes_served,status_code,path)"
        " VALUES (?,?,?,?,?,?,?,?)",
        (token, mode, get_ip(),
         request.headers.get("User-Agent","")[:500],
         request.headers.get("Referer","")[:500],
         nb, status, (path or request.path)[:500]), fetch=False)
    if nb > 0:
        db_exec("INSERT INTO bandwidth_log (ip_address,bytes_used,log_date) VALUES (?,?,date('now'))",
                (get_ip(), nb), fetch=False)

def is_blocked(ip):
    r = q1("SELECT id FROM blocked_ips WHERE ip_address=?"
           " AND (unblock_at IS NULL OR unblock_at>datetime('now'))", (ip,))
    return r is not None

def record_fail(ip, username=""):
    db_exec("INSERT INTO failed_logins (ip_address,username) VALUES (?,?)", (ip,username), fetch=False)
    cutoff = (datetime.now()-timedelta(minutes=CFG["BAN_MINUTES"])).strftime("%Y-%m-%d %H:%M:%S")
    cnt = q1("SELECT COUNT(*) c FROM failed_logins WHERE ip_address=? AND attempt_at>?", (ip,cutoff))
    if cnt and cnt["c"] >= CFG["MAX_LOGIN_FAIL"]:
        unblock = (datetime.now()+timedelta(minutes=CFG["BAN_MINUTES"])).strftime("%Y-%m-%d %H:%M:%S")
        db_exec("INSERT OR IGNORE INTO blocked_ips (ip_address,reason,unblock_at) VALUES (?,?,?)",
                (ip, "Too many failed logins", unblock), fetch=False)
        telegram_send(f"🚫 IP bloklandi: {ip}\nSabab: {CFG['MAX_LOGIN_FAIL']} marta xato login urinishi")
        return True
    return False

def clear_fails(ip):
    db_exec("DELETE FROM failed_logins WHERE ip_address=?", (ip,), fetch=False)

def mode_on(mode):
    r = q1("SELECT is_enabled FROM mode_settings WHERE mode=?", (mode,))
    return bool(r and r["is_enabled"])

def check_link(token, pw=None):
    lk = q1("SELECT * FROM links WHERE token=? AND is_active=1", (token,))
    if not lk: return None, "Havola topilmadi yoki o'chirilgan"
    if lk.get("expires_at"):
        try:
            if datetime.now() > datetime.strptime(lk["expires_at"], "%Y-%m-%d %H:%M:%S"):
                return None, "Havolaning muddati tugagan"
        except: pass
    if not mode_on(lk["mode"]):
        return None, f"Rejim ({lk['mode']}) o'chirilgan"
    if lk.get("password_hash"):
        if pw is None: return None, "NEED_PASSWORD"
        if not check_password_hash(lk["password_hash"], pw):
            return None, "Noto'g'ri parol"
    return lk, None

def admin_req(f):
    @wraps(f)
    def d(*a,**k):
        if not session.get("admin"): return redirect("/login")
        if is_blocked(get_ip()): abort(403)
        return f(*a,**k)
    return d

def user_req(f):
    @wraps(f)
    def d(*a,**k):
        if "user_id" not in session: return redirect("/login")
        return f(*a,**k)
    return d

def allowed(fn):
    return Path(fn).suffix.lower() in CFG["ALLOWED_EXT"]

def hsize(b):
    b = b or 0
    for u in ["B","KB","MB","GB"]:
        if b<1024: return f"{b:.1f} {u}"
        b/=1024
    return f"{b:.1f} TB"

def gtok(n=32): return secrets.token_urlsafe(n)

def local_ip():
    try:
        s=socket.socket(socket.AF_INET,socket.SOCK_DGRAM)
        s.connect(("8.8.8.8",80)); ip=s.getsockname()[0]; s.close(); return ip
    except: return "127.0.0.1"

def get_ssid():
    try:
        if platform.system()=="Windows":
            out=subprocess.check_output("netsh wlan show interfaces",shell=True,
                stderr=subprocess.DEVNULL).decode("cp1251",errors="ignore")
            for l in out.splitlines():
                if "SSID" in l and "BSSID" not in l:
                    return l.split(":",1)[-1].strip()
        elif platform.system()=="Linux":
            return subprocess.check_output("iwgetid -r",shell=True,
                stderr=subprocess.DEVNULL).decode().strip()
    except: pass
    return "Noma'lum WiFi"

def expiry_checker():
    while True:
        time.sleep(300)
        try:
            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            db_exec("UPDATE links SET is_active=0 WHERE expires_at IS NOT NULL AND expires_at<? AND is_active=1",
                    (now,), fetch=False)
        except: pass

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║           XAVFSIZLIK: CSRF, RBAC (rollar), API-kalit, 2FA                ║
# ╚══════════════════════════════════════════════════════════════════════════╝
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"  # fetch()/JSON endpointlar uchun CSRF asosiy himoyasi

def get_csrf_token():
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_hex(24)
    return session["_csrf"]

def csrf_field():
    """HTML <form>lar ichiga qo'yiladigan yashirin CSRF maydoni."""
    return f'<input type="hidden" name="_csrf" value="{get_csrf_token()}">'

_CSRF_EXEMPT_PATHS = {"/login", "/register", "/p"}  # public parol-himoyalangan havola formasi kabi

@app.before_request
def _csrf_protect():
    if request.method != "POST":
        return None
    # JSON fetch so'rovlari uchun maxsus sarlavha yoki to'g'ri CSRF token talab qilinadi.
    # SameSite=Lax cookie sozlamasi (yuqorida) fetch() orqali cross-site holatlarni allaqachon bloklaydi;
    # bu yerda esa klassik HTML formalar uchun qo'shimcha tekshiruv qilinadi.
    if request.path.startswith("/p/"):
        return None  # ochiq havola parol formasi — token yo'q, alohida himoyalangan
    tok = request.form.get("_csrf") or request.headers.get("X-CSRF-Token")
    if request.is_json or request.content_type == "application/json":
        tok = request.headers.get("X-CSRF-Token") or tok
    sess_tok = session.get("_csrf")
    # Login/registerda hali sessiya yo'q — parol/urinish cheklovi (rate-limit) allaqachon himoya qiladi.
    if request.path in ("/login", "/register"):
        return None
    if sess_tok and tok != sess_tok:
        abort(403)
    return None

# ── RBAC: rollar — admin > editor > user > viewer (faqat ko'rish) ─────────
ROLE_RANK = {"viewer": 0, "user": 1, "editor": 2, "admin": 3}

def role_rank(role):
    return ROLE_RANK.get(role or "user", 1)

def write_req(f):
    """Faqat 'viewer' bo'lmagan (ya'ni yozish huquqiga ega) foydalanuvchilar uchun."""
    @wraps(f)
    def d(*a, **k):
        if role_rank(session.get("role")) < ROLE_RANK["user"]:
            abort(403)
        return f(*a, **k)
    return d

# ── Guest / loginsiz kirish rejimi ─────────────────────────────────────────
@app.before_request
def _guest_autologin():
    if session.get("user_id"):
        return None
    if get_setting("require_login", "1") == "0":
        session["user_id"] = 0
        session["username"] = "mehmon"
        session["role"] = "viewer"
        session["admin"] = False
        session["_guest"] = True
    return None

# ── API kalitlari (Bearer token) ───────────────────────────────────────────
def new_api_key(user_id, name=""):
    raw = "sk_" + secrets.token_urlsafe(32)
    prefix = raw[:10]
    h = hashlib.sha256(raw.encode()).hexdigest()
    db_exec("INSERT INTO api_keys (user_id,name,key_prefix,key_hash) VALUES (?,?,?,?)",
            (user_id, name or "API kalit", prefix, h), fetch=False)
    return raw  # faqat shu safar to'liq ko'rsatiladi

def api_key_req(f):
    @wraps(f)
    def d(*a, **k):
        auth = request.headers.get("Authorization", "")
        if not auth.startswith("Bearer "):
            return jsonify({"error": "Authorization: Bearer <API_KEY> talab qilinadi"}), 401
        raw = auth[7:].strip()
        h = hashlib.sha256(raw.encode()).hexdigest()
        row = q1("SELECT * FROM api_keys WHERE key_hash=? AND revoked=0", (h,))
        if not row:
            return jsonify({"error": "API kalit noto'g'ri yoki bekor qilingan"}), 401
        db_exec("UPDATE api_keys SET last_used_at=datetime('now') WHERE id=?", (row["id"],), fetch=False)
        request.api_user_id = row["user_id"]
        return f(*a, **k)
    return d

# ── 2FA (Telegram bir martalik kod) ────────────────────────────────────────
def send_2fa_code(user):
    code = f"{secrets.randbelow(1000000):06d}"
    exp = (datetime.now() + timedelta(minutes=5)).strftime("%Y-%m-%d %H:%M:%S")
    db_exec("INSERT INTO two_fa_codes (user_id,code,expires_at) VALUES (?,?,?)", (user["id"], code, exp), fetch=False)
    chat = user.get("tg_chat_id") or get_setting("tg_chat", CFG["TELEGRAM_CHAT_ID"])
    token = get_setting("tg_token", CFG["TELEGRAM_TOKEN"])
    if token and chat:
        def _send():
            try:
                url = f"https://api.telegram.org/bot{token}/sendMessage"
                data = urllib.parse.urlencode({"chat_id": chat, "text": f"🔑 Tasdiqlash kodi: {code} (5 daqiqa amal qiladi)"}).encode()
                urllib.request.urlopen(urllib.request.Request(url, data=data), timeout=6)
            except Exception as e:
                print(_c(f"[2FA/Telegram] {e}", R))
        threading.Thread(target=_send, daemon=True).start()
    return code

def verify_2fa_code(user_id, code):
    row = q1("SELECT * FROM two_fa_codes WHERE user_id=? AND code=? AND used=0 AND expires_at>datetime('now') ORDER BY id DESC LIMIT 1",
             (user_id, code))
    if not row: return False
    db_exec("UPDATE two_fa_codes SET used=1 WHERE id=?", (row["id"],), fetch=False)
    return True

def finalize_login(user, ip):
    clear_fails(ip)
    session.permanent = True
    session.update({"user_id": user["id"], "username": user["username"],
                     "role": user["role"], "admin": user["role"] == "admin", "_guest": False})
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    db_exec("UPDATE users SET last_login=? WHERE id=?", (now, user["id"]), fetch=False)
    telegram_send(f"✅ Yangi kirish\nFoydalanuvchi: {user['username']}\nIP: {ip}")

# ── Sozlamalar (key-value) ────────────────────────────────
def get_setting(key, default=""):
    r = q1("SELECT value FROM app_settings WHERE key=?", (key,))
    return r["value"] if r else default

def set_setting(key, value):
    db_exec("INSERT INTO app_settings (key,value) VALUES (?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, value), fetch=False)

# ── Telegram bildirishnoma ────────────────────────────────
def telegram_send(text):
    """Sozlamalarda yoqilgan bo'lsa, Telegram botga xabar yuboradi."""
    if get_setting("tg_enabled", "0") != "1":
        return
    token = get_setting("tg_token", CFG["TELEGRAM_TOKEN"])
    chat  = get_setting("tg_chat", CFG["TELEGRAM_CHAT_ID"])
    if not token or not chat:
        return
    def _send():
        try:
            url = f"https://api.telegram.org/bot{token}/sendMessage"
            data = urllib.parse.urlencode({"chat_id": chat, "text": text}).encode()
            urllib.request.urlopen(urllib.request.Request(url, data=data), timeout=6)
        except Exception as e:
            print(_c(f"[Telegram] {e}", R))
    threading.Thread(target=_send, daemon=True).start()

# ── Serverni saytdan yoqish/o'chirish (umumiy kirish) ──────────────────────
def server_enabled():
    return get_setting("server_enabled", "1") == "1"

@app.before_request
def _check_server_enabled():
    if server_enabled():
        return None
    if request.path in ("/login", "/logout") or request.path.startswith("/static"):
        return None
    if session.get("admin"):
        return None
    return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
    <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center}}</style>
    </head><body><div>
    <p style="font-size:2.5rem">🛑</p>
    <h1 style="color:var(--rd);margin:10px 0">Server vaqtincha o'chirilgan</h1>
    <p class="tm">Administrator serverga umumiy kirishni vaqtincha to'xtatgan.<br>Birozdan so'ng qayta urinib ko'ring.</p>
    <a href="/login" class="btn bgh mt">Admin sifatida kirish</a>
    </div></body></html>""", 503

# ── Ko'p fayl/papkali loyiha fayl tizimi (virtual FS, SQLite ichida) ───────
def _proj_or_404(puuid, uid, adm):
    proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
    if not proj: abort(404)
    if proj["owner_id"] != uid and not adm: abort(403)
    return proj

def _seed_default_files(project_id):
    defaults = [
        ("index.html", 0, '<!DOCTYPE html>\n<html lang="uz">\n<head>\n  <meta charset="UTF-8">\n'
                           '  <title>Sahifa</title>\n  <link rel="stylesheet" href="style.css">\n</head>\n<body>\n'
                           '  <h1>Salom Dunyo!</h1>\n  <script src="script.js"></script>\n</body>\n</html>'),
        ("style.css", 0, "/* CSS kodingiz */\nbody{font-family:sans-serif;background:#fafafa;color:#222;}"),
        ("script.js", 0, "// JS kodingiz\nconsole.log('Loyiha ishga tushdi!');"),
    ]
    for path, is_folder, content in defaults:
        db_exec("INSERT OR IGNORE INTO project_files (project_id,path,is_folder,content) VALUES (?,?,?,?)",
                (project_id, path, is_folder, content), fetch=False)

def _ensure_files(project_id):
    r = q1("SELECT COUNT(*) c FROM project_files WHERE project_id=?", (project_id,))
    if not r or not r["c"]:
        _seed_default_files(project_id)

def _resolve_rel(base, rel):
    rel = rel.lstrip("/")
    base_dir = base.rsplit("/", 1)[0] + "/" if "/" in base else ""
    parts = (base_dir + rel).split("/")
    out = []
    for p in parts:
        if p == "..":
            if out: out.pop()
        elif p not in ("", "."):
            out.append(p)
    return "/".join(out)

def _build_page_html(files_map, entry_path):
    html = files_map.get(entry_path)
    if html is None: return None
    def repl_css(m):
        href = m.group(1)
        if href.startswith("http"): return m.group(0)
        c = files_map.get(_resolve_rel(entry_path, href))
        return f"<style>{c}</style>" if c is not None else m.group(0)
    def repl_js(m):
        src = m.group(1)
        if src.startswith("http"): return m.group(0)
        c = files_map.get(_resolve_rel(entry_path, src))
        return f"<script>{c}</script>" if c is not None else m.group(0)
    html = re.sub(r'<link[^>]+href=["\']([^"\'>]+\.css)["\'][^>]*>', repl_css, html, flags=re.I)
    html = re.sub(r'<script[^>]+src=["\']([^"\'>]+\.js)["\'][^>]*></script>', repl_js, html, flags=re.I)
    return html

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                          HTML / CSS                                      ║
# ╚══════════════════════════════════════════════════════════════════════════╝
CSS = """
:root{--bg:#0d0f18;--surf:#161929;--card:#1c2136;--brd:#252d45;
  --ac:#7c6fff;--ac2:#5548e0;--gr:#22d3a0;--rd:#f05d5d;
  --yl:#f5c518;--tx:#d4daf0;--mt:#5c6890;--r:10px}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:'Segoe UI',system-ui,sans-serif;background:var(--bg);color:var(--tx);min-height:100vh;font-size:14px}
a{color:var(--ac);text-decoration:none} a:hover{color:#a89fff}
.layout{display:flex;min-height:100vh}
.sb{width:220px;background:var(--surf);border-right:1px solid var(--brd);
  flex-shrink:0;position:sticky;top:0;height:100vh;overflow-y:auto;display:flex;flex-direction:column}
.sb .logo{padding:18px;font-size:1.05rem;font-weight:700;color:#fff;
  border-bottom:1px solid var(--brd)}
.sb .logo span{color:var(--ac)}
.sb nav a{display:flex;align-items:center;gap:9px;padding:9px 18px;
  color:var(--mt);font-size:.85rem;transition:.15s;border-left:3px solid transparent}
.sb nav a:hover,.sb nav a.act{color:var(--tx);background:rgba(124,111,255,.08);border-left-color:var(--ac)}
.sb nav .sep{padding:12px 18px 4px;font-size:.68rem;letter-spacing:.1em;color:var(--mt);text-transform:uppercase}
.main{flex:1;display:flex;flex-direction:column;overflow-x:hidden}
.top{background:var(--surf);border-bottom:1px solid var(--brd);
  padding:11px 24px;display:flex;align-items:center;justify-content:space-between;gap:12px}
.top h1{font-size:.95rem;font-weight:600;color:#fff;white-space:nowrap}
.srch input{width:100%;padding:7px 14px;background:var(--bg);border:1px solid var(--brd);
  border-radius:20px;color:var(--tx);font-size:.8rem;outline:none;transition:.15s}
.srch input:focus{border-color:var(--ac)}
.cnt{padding:22px;flex:1}
.card{background:var(--card);border:1px solid var(--brd);border-radius:var(--r);padding:18px;margin-bottom:14px}
.card h3{font-size:.87rem;color:#fff;margin-bottom:12px;font-weight:600}
.g{display:grid;gap:14px} .g2{grid-template-columns:1fr 1fr}
.g3{grid-template-columns:1fr 1fr 1fr} .g4{grid-template-columns:repeat(4,1fr)}
.stat{background:var(--card);border:1px solid var(--brd);border-radius:var(--r);padding:16px;text-align:center}
.stat .v{font-size:1.7rem;font-weight:800;color:var(--ac)} .stat .l{font-size:.73rem;color:var(--mt);margin-top:3px}
.btn{display:inline-flex;align-items:center;gap:5px;padding:7px 14px;border-radius:7px;
  font-size:.8rem;font-weight:600;cursor:pointer;border:none;transition:.15s;white-space:nowrap}
.bp{background:var(--ac);color:#fff} .bp:hover{background:var(--ac2);color:#fff}
.bg{background:#0d6b51;color:var(--gr)} .bg:hover{background:#0a8464;color:#fff}
.br{background:#5c1a1a;color:var(--rd)} .br:hover{background:#7a1e1e;color:#fff}
.bgh{background:transparent;border:1px solid var(--brd);color:var(--mt)}
.bgh:hover{border-color:var(--ac);color:var(--ac)}
.bsm{padding:5px 10px;font-size:.76rem}
.fld{margin-bottom:12px}
.fld label{display:block;margin-bottom:4px;color:var(--mt);font-size:.78rem;font-weight:600}
.fld input,.fld select,.fld textarea{width:100%;padding:8px 11px;background:var(--bg);
  border:1px solid var(--brd);border-radius:7px;color:var(--tx);font-size:.85rem;outline:none;transition:.15s}
.fld input:focus,.fld select:focus,.fld textarea:focus{border-color:var(--ac)}
.fld textarea{min-height:90px;resize:vertical}
.row{display:flex;gap:10px;align-items:flex-end;flex-wrap:wrap}
.tw{overflow-x:auto;border-radius:var(--r);border:1px solid var(--brd)}
table{width:100%;border-collapse:collapse}
th,td{padding:10px 13px;text-align:left;font-size:.8rem;border-bottom:1px solid var(--brd)}
th{color:var(--mt);font-weight:600;background:rgba(255,255,255,.02)} td{color:var(--tx)}
tr:last-child td{border-bottom:none} tr:hover td{background:rgba(124,111,255,.04)}
.bx{display:inline-flex;align-items:center;gap:4px;padding:2px 8px;border-radius:20px;font-size:.7rem;font-weight:600}
.xg{background:#0a3d2e;color:var(--gr)} .xr{background:#3b1010;color:var(--rd)}
.xy{background:#3b2e05;color:var(--yl)} .xb{background:#0d1f40;color:#60a5fa}
.xp{background:#1e1040;color:#c4b5fd} .xm{background:#1a1f30;color:var(--mt)}
.al{padding:11px 15px;border-radius:var(--r);margin-bottom:14px;font-size:.83rem}
.al-ok{background:#0a3d2e;color:var(--gr);border:1px solid #0d5a40}
.al-er{background:#3b1010;color:var(--rd);border:1px solid #5c1a1a}
.fl{display:flex;align-items:center;gap:9px;flex-wrap:wrap}
.mla{margin-left:auto} .mt{margin-top:14px} .mb{margin-bottom:14px}
.tm{color:var(--mt)} .tg{color:var(--gr)} .tr{color:var(--rd)}
.cpb{background:transparent;border:1px solid var(--brd);color:var(--mt);
  border-radius:5px;padding:2px 7px;font-size:.7rem;cursor:pointer;transition:.15s}
.cpb:hover{border-color:var(--ac);color:var(--ac)}
.mcard{border:2px solid var(--brd);border-radius:12px;padding:18px;transition:.2s}
.mcard.on{border-color:var(--gr);background:rgba(34,211,160,.03)}
.urlbox{background:var(--bg);border:1px solid var(--brd);border-radius:6px;
  padding:7px 11px;font-family:monospace;font-size:.75rem;color:var(--ac);
  margin-top:10px;word-break:break-all}
.mongrid{display:grid;grid-template-columns:repeat(4,1fr);gap:14px}
.monbar{background:var(--bg);border-radius:6px;height:9px;overflow:hidden;margin-top:8px}
.monfill{height:100%;border-radius:6px;transition:width .4s}
@media(max-width:768px){.layout{flex-direction:column}.sb{width:100%;height:auto;position:static}
  .g2,.g3,.g4,.mongrid{grid-template-columns:1fr} .srch{display:none}}
"""

def _nav(href, label, active):
    return f'<a href="{href}" class="{"act" if active else ""}">{label}</a>'

def _pg(title, body, act="dash", flash=None, ftype="ok"):
    adm   = session.get("admin", False)
    uname = session.get("username", "")
    role  = session.get("role", "user")
    site_title = get_setting("site_title", "SrvManager")
    fl    = f'<div class="al al-{ftype}">{flash}</div>' if flash else ""
    adm_nav = ""
    if adm:
        adm_nav = f"""
        <div class="sep">Admin</div>
        {_nav('/admin/users','👥 Foydalanuvchilar','users'==act)}
        {_nav('/admin/logs','📋 Kirish loglari','logs'==act)}
        {_nav('/admin/blocked','🚫 Bloklangan IP','blocked'==act)}
        {_nav('/admin/bandwidth','📊 Bandwidth','bw'==act)}
        {_nav('/admin/monitor','📟 Monitoring','monitor'==act)}
        {_nav('/admin/uptime','📉 Uptime','uptime'==act)}
        {_nav('/admin/backend/logs','🐍 Backend','backend'==act)}
        {_nav('/admin/audit','📝 Audit','audit'==act)}
        {_nav('/admin/ip-whitelist','🔒 IP Whitelist','ipwl'==act)}
        {_nav('/admin/domains','🌐 Domenlar','domains'==act)}
        {_nav('/admin/settings','⚙️ Sozlamalar','settings'==act)}"""
    rb = f'<span class="bx {"xg" if adm else "xb"}">{role}</span>'
    return f"""<!DOCTYPE html>
<html lang="uz"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} — {site_title}</title>
<style>{CSS}</style>
</head><body>
<div class="layout">
<aside class="sb">
  <div class="logo">⬡ <span>{site_title}</span></div>
  <nav>
    {_nav('/dashboard','🏠 Dashboard','dash'==act)}
    <div class="sep">Rejimlar</div>
    {_nav('/modes','🔀 Rejimlar','modes'==act)}
    {_nav('/links','🔗 Havolalar','links'==act)}
    <div class="sep">Kontent</div>
    {_nav('/files','📁 Fayllar','files'==act)}
    {_nav('/projects','💻 Loyihalar','projects'==act)}
    {_nav('/editor/new','✏️ Muharrir','editor'==act)}
    <div class="sep">AI</div>
    <a href="#" onclick="toggleAIWindow();return false;" class="{'act' if act=='ai' else ''}">🤖 AI Yordamchi</a>
    <div class="sep">Hisobot</div>
    {_nav('/stats','📈 Statistika','stats'==act)}
    {adm_nav}
    <div class="sep">Hisob</div>
    {_nav('/profile',f'👤 {uname}','profile'==act)}
    {_nav('/logout','🚪 Chiqish',False)}
  </nav>
</aside>
<div class="main">
  <div class="top"><h1>{title}</h1>
    <form method="GET" action="/search" class="srch" style="flex:1;max-width:320px">
      <input name="q" placeholder="🔍 Havola, fayl, loyiha qidirish...">
    </form>
    <div class="fl">{rb}<span class="tm" style="font-size:.78rem">{uname}</span>
    <span class="bx xm" style="font-size:.65rem">SQLite</span></div>
  </div>
  <div class="cnt">{fl}{body}</div>
</div>
</div>
<script>
function copyText(t){{navigator.clipboard.writeText(t).then(()=>{{
  const e=event.target;const o=e.textContent;e.textContent='✓ Nusxalandi!';
  setTimeout(()=>e.textContent=o,1500);}});}}
</script>
<!-- AI YORDAMCHI FLOATING WINDOW -->
<div id="aiWindow" style="display:none;position:fixed;bottom:20px;right:20px;width:380px;height:480px;
  background:#161929;border:1px solid #252d45;border-radius:14px;box-shadow:0 12px 40px rgba(0,0,0,.6);
  z-index:999999;display:none;flex-direction:column;overflow:hidden;min-width:260px;min-height:200px;resize:both;font-size:14px">
  <div id="aiHeader" style="padding:10px 14px;background:#1c2136;border-bottom:1px solid #252d45;
    cursor:move;display:flex;align-items:center;gap:8px;flex-shrink:0;user-select:none">
    <button onclick="openAITrainPanel()" style="background:transparent;border:1px solid #252d45;color:#7c6fff;
      border-radius:5px;padding:3px 8px;font-size:.7rem;cursor:pointer" title="AI ni o'qitish">📚 O'qitish</button>
    <button onclick="closeAIWindow()" style="background:transparent;border:1px solid #252d45;color:#f05d5d;
      border-radius:5px;padding:3px 8px;font-size:.75rem;cursor:pointer;font-weight:700">✕</button>
    <span style="font-size:1.1rem;margin-left:4px">🤖</span>
    <b style="color:#fff;font-size:.85rem;flex:1">AI Yordamchi</b>
  </div>
  <div style="padding:4px 12px;display:flex;gap:4px;border-bottom:1px solid #1c2136;flex-shrink:0">
    <button onclick="loadAIChatHistory()" style="background:transparent;border:1px solid #252d45;color:#5c6890;border-radius:4px;padding:2px 6px;font-size:.65rem;cursor:pointer">📜 Tarix</button>
    <button onclick="clearAIChat()" style="background:transparent;border:1px solid #252d45;color:#5c6890;border-radius:4px;padding:2px 6px;font-size:.65rem;cursor:pointer">🗑 Tozalash</button>
    <button onclick="sendAIImage()" style="background:transparent;border:1px solid #252d45;color:#5c6890;border-radius:4px;padding:2px 6px;font-size:.65rem;cursor:pointer">🖼 Rasm</button>
    <button onclick="showAITutorial()" style="background:transparent;border:1px solid #252d45;color:#f5c518;border-radius:4px;padding:2px 6px;font-size:.65rem;cursor:pointer">📖 Qo'llanma</button>
  </div>
  <div id="aiMessages" style="flex:1;overflow-y:auto;padding:12px;display:flex;flex-direction:column;gap:8px"></div>
  <div style="padding:8px 12px;border-top:1px solid #252d45;display:flex;gap:6px;flex-shrink:0">
    <input type="text" id="aiInput" placeholder="Savol yozing..."
      style="flex:1;padding:8px 12px;background:#0d0f18;border:1px solid #252d45;border-radius:8px;
      color:#d4daf0;font-size:.82rem;outline:none" onkeydown="if(event.key==='Enter')askAI()">
    <button onclick="speakLastAI()" title="Ovozli o'qish" style="background:transparent;border:1px solid #252d45;color:#5c6890;
      border-radius:8px;padding:8px;font-size:.9rem;cursor:pointer">🔊</button>
    <button onclick="askAI()" style="background:#7c6fff;color:#fff;border:none;border-radius:8px;
      padding:8px 14px;font-size:.8rem;cursor:pointer;font-weight:600">↑</button>
  </div>
</div>
<!-- AI TRAIN PANEL -->
<div id="aiTrainBg" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.55);
  z-index:9999999;display:none;align-items:center;justify-content:center"
  onclick="if(event.target.id==='aiTrainBg')closeAITrain()">
  <div style="background:#1c2136;border:1px solid #252d45;border-radius:12px;width:92%;max-width:560px;
    max-height:80vh;display:flex;flex-direction:column;overflow:hidden">
    <div style="padding:12px 14px;border-bottom:1px solid #252d45;display:flex;align-items:center">
      <b style="color:#fff">📚 AI ni o'qitish</b>
      <button onclick="closeAITrain()" style="margin-left:auto;background:transparent;border:1px solid #252d45;
        color:#f05d5d;border-radius:5px;padding:3px 8px;cursor:pointer">✕</button>
    </div>
    <div style="padding:14px;overflow-y:auto">
      <p style="color:#5c6890;font-size:.79rem;margin-bottom:12px">AI ni 3 xil usulda o'rgating.
        Barcha ma'lumotlar <code>ai_data/</code> papkasida saqlanadi.</p>
      <!-- TAB BUTTONS -->
      <div style="display:flex;gap:4px;margin-bottom:12px;flex-wrap:wrap">
        <button onclick="showAITab('qa')" id="aiTabQA" style="flex:1;padding:6px;background:#7c6fff;color:#fff;border:none;border-radius:6px;cursor:pointer;font-size:.72rem;font-weight:600">📝 Savol-Javob</button>
        <button onclick="showAITab('badword')" id="aiTabBADWORD" style="flex:1;padding:6px;background:#252d45;color:#5c6890;border:none;border-radius:6px;cursor:pointer;font-size:.72rem">🚫 Filtr</button>
      </div>
      <!-- QA TAB -->
      <div id="aiPanelQA">
        <div style="margin-bottom:8px"><label style="color:#5c6890;font-size:.74rem">Savol / kalit so'z:</label>
          <input type="text" id="aiTrainQ" placeholder="Masalan: server qanday ishga tushadi?"
            style="width:100%;padding:7px;background:#0d0f18;border:1px solid #252d45;border-radius:6px;color:#d4daf0;margin-top:3px;font-size:.82rem"></div>
        <div style="margin-bottom:8px"><label style="color:#5c6890;font-size:.74rem">Javob (HTML, rasm uchun &lt;img src="url"&gt; ishlatish mumkin):</label>
          <textarea id="aiTrainA" rows="3" placeholder="Javob matni... Rasm uchun: <img src=&quot;https://...&quot;>"
            style="width:100%;padding:7px;background:#0d0f18;border:1px solid #252d45;border-radius:6px;color:#d4daf0;margin-top:3px;resize:vertical;font-size:.82rem"></textarea></div>
        <button onclick="trainAI('qa')" style="background:#7c6fff;color:#fff;border:none;border-radius:7px;padding:7px 14px;cursor:pointer;font-weight:600;font-size:.8rem">💾 Saqlash</button>
      </div>
      <!-- TOPIC TAB (hidden but functional) -->
      <div id="aiPanelTopic" style="display:none"></div>
      <!-- WORD TAB (hidden but functional) -->
      <div id="aiPanelWord" style="display:none"></div>
      <!-- BADWORD TAB -->
      <div id="aiPanelBadword" style="display:none">
        <p style="color:#5c6890;font-size:.74rem;margin-bottom:8px">Haqoratli so'zlarni qo'shing. Foydalanuvchi bu so'zlarni ishlatsa, siz belgilagan javob yuboriladi.</p>
        <div style="margin-bottom:8px"><label style="color:#5c6890;font-size:.74rem">Haqoratli so'z:</label>
          <input type="text" id="aiBadWord" placeholder="Masalan: axmoq"
            style="width:100%;padding:7px;background:#0d0f18;border:1px solid #252d45;border-radius:6px;color:#d4daf0;margin-top:3px;font-size:.82rem"></div>
        <div style="margin-bottom:8px"><label style="color:#5c6890;font-size:.74rem">Javob (bu so'z ishlatilganda nima deyilsin):</label>
          <input type="text" id="aiBadResp" placeholder="Masalan: Iltimos, hurmatli muloqot qiling!"
            style="width:100%;padding:7px;background:#0d0f18;border:1px solid #252d45;border-radius:6px;color:#d4daf0;margin-top:3px;font-size:.82rem"></div>
        <button onclick="trainAI('badword')" style="background:#f05d5d;color:#fff;border:none;border-radius:7px;padding:7px 14px;cursor:pointer;font-weight:600;font-size:.8rem">🚫 Qo'shish</button>
        <div id="aiBadList" style="display:flex;flex-wrap:wrap;gap:4px;margin-top:8px"></div>
      </div>
      <button onclick="loadAIKnowledge()" style="background:transparent;border:1px solid #252d45;color:#5c6890;border-radius:7px;
        padding:6px 12px;cursor:pointer;font-size:.78rem;margin-top:10px">🔄 Yangilash</button>
    </div>
    <div id="aiKnowledgeList" style="border-top:1px solid #252d45;overflow-y:auto;max-height:30vh;padding:8px"></div>
  </div>
</div>
<script>
var aiWindowEl=null,aiDragging=false,aiDragX=0,aiDragY=0,aiStartX=0,aiStartY=0;
function toggleAIWindow(){{
  var w=document.getElementById('aiWindow');
  if(w.style.display==='flex'){{w.style.display='none';}}
  else{{w.style.display='flex';document.getElementById('aiInput').focus();loadAIChatHistory();}}
}}
function closeAIWindow(){{document.getElementById('aiWindow').style.display='none';}}
function loadAIChatHistory(){{
  fetch('/api/ai/history',{{headers:{{'X-CSRF-Token':'{get_csrf_token()}'}}}}).then(r=>r.json()).then(d=>{{
    var msgs=document.getElementById('aiMessages');
    msgs.innerHTML='';
    (d.history||[]).slice(-20).forEach(function(m){{
      addAIMsg(m.q,'user');
      addAIMsg(m.a,'ai');
    }});
    if(!(d.history||[]).length) addAIMsg('Salom! Men AI yordamchiman. 🤖 Sizga qanday yordam bera olaman?','ai');
    msgs.scrollTop=msgs.scrollHeight;
  }}).catch(function(){{
    addAIMsg('Salom! Men AI yordamchiman. 🤖 Sizga qanday yordam bera olaman?','ai');
  }});
}}
function clearAIChat(){{
  if(!confirm('Suhbat tarixini tozalashni xohlaysizmi?')) return;
  fetch('/api/ai/history/clear',{{method:'POST',headers:{{'X-CSRF-Token':'{get_csrf_token()}'}}}}).then(function(){{
    document.getElementById('aiMessages').innerHTML='';
    addAIMsg('Suhbat tozalandi. Yangi suhbat boshlaymiz! 🤖','ai');
  }});
}}
function sendAIImage(){{
  var url=prompt('Rasm URL manzilini kiriting:');
  if(!url) return;
  var msgs=document.getElementById('aiMessages');
  var div=document.createElement('div');
  div.style.cssText='align-self:flex-end;max-width:85%';
  div.innerHTML='<img src="'+url+'" style="max-width:100%;border-radius:8px;border:1px solid #252d45">';
  msgs.appendChild(div);
  msgs.scrollTop=msgs.scrollHeight;
  // AI ga rasm haqida xabar
  addAIMsg('🖼 Rasm qabul qilindi! Chiroyli rasm.','ai');
}}
function showAITutorial(){{
  var tutorial='📖 **AI YORDAMCHI QO\\'LLANMASI**\\n\\n'
    +'---\\n'
    +'==MATN FORMATLASH:==\\n'
    +'• `**qalin matn**` → **qalin matn**\\n'
    +'• `*kursiv matn*` → *kursiv matn*\\n'
    +'• `__tagiga chiziq__` → __tagiga chiziq__\\n'
    +'• `~~ustiga chiziq~~` → ~~ustiga chiziq~~\\n'
    +'• `==sariq marker==` → ==sariq marker==\\n'
    +'• `!!qizil muhim!!` → !!qizil muhim!!\\n'
    +'• `@@yashil@@` → @@yashil@@\\n'
    +'• `##ko\\'k rang##` → ##ko\\'k rang##\\n'
    +'• ` \\`kod\\` ` → `inline kod`\\n'
    +'• ` \\`\\`\\`kod blok\\`\\`\\` ` → kod bloki\\n'
    +'• `[havola](url)` → havola\\n'
    +'• `---` → ajratuvchi chiziq\\n'
    +'• `> iqtibos` → iqtibos bloki\\n\\n'
    +'---\\n'
    +'==RASMLAR BILAN ISHLASH:==\\n'
    +'• 🖼 Rasm tugmasi → URL kiritib rasm yuborish\\n'
    +'• O\\'qitishda javobga: `<img src="url">` yozing\\n'
    +'• AI javobida rasm avtomatik ko\\'rinadi\\n\\n'
    +'---\\n'
    +'==KALIT SO\\'ZLAR:==\\n'
    +'• **Salomlashish:** salom, hi, hello, qalay\\n'
    +'• **HTML:** "div nima", "img tegi", "table"\\n'
    +'• **CSS:** "flexbox nima", "margin", "grid"\\n'
    +'• **Emmet:** "div*10 nima", "ul>li*5", "emmet"\\n'
    +'• **Matematik:** 2+2, 100/4, (5+3)*2\\n'
    +'• **O\\'yin:** tosh, qaychi, qogoz, latifa, son ber\\n'
    +'• **Son topish:** "son top" (1-100 topishmoq)\\n'
    +'• **Lorem:** "lorem 50" (placeholder matn)\\n'
    +'• **Vaqt:** "soat nechchi", "bugun nechanchi"\\n'
    +'• **Eslatma:** "5 daqiqadan keyin eslatib tur"\\n'
    +'• **Loyiha:** "nechta fayl", "loyihalarim"\\n'
    +'• **Xotira:** "oldin nima dedim", "esla", "tarix"\\n'
    +'• **Haqida:** "sen kim", "isming nima", "nima qila olasan"\\n\\n'
    +'---\\n'
    +'==O\\'QITISH:==\\n'
    +'• 📚 O\\'qitish tugmasini bosing\\n'
    +'• Savol va javob kiriting\\n'
    +'• Javobda formatlash ishlatish mumkin\\n'
    +'• Javobda `<img src="url">` bilan rasm qo\\'shish mumkin\\n'
    +'• 🚫 Filtr tabida haqoratli so\\'zlarni boshqaring\\n\\n'
    +'---\\n'
    +'==YANGI FUNKSIYALAR:==\\n'
    +'• 📐 **Lorem:** "lorem 50" — 50 so\\'zlik placeholder matn\\n'
    +'• 🎯 **Son topish:** "son top" — 1-100 orasida topishmoq\\n'
    +'• 📁 **Loyiha:** "nechta fayl", "loyihalarim" — fayl haqida\\n'
    +'• ⏰ **Eslatma:** "5 daqiqadan keyin eslatib tur" — timer\\n'
    +'• 🔊 **Ovozli:** 🔊 tugmasini bosing — AI javobini o\\'qiydi\\n'
    +'• 🕐 **Vaqt:** "soat nechchi", "bugun nechanchi"\\n\\n'
    +'---\\n'
    +'@@Omadli foydalanish!@@ 🚀';
  var msgs=document.getElementById('aiMessages');
  msgs.innerHTML='';
  addAIMsg(tutorial,'ai');
}}
function openAITrainPanel(){{document.getElementById('aiTrainBg').style.display='flex';loadAIKnowledge();}}
function closeAITrain(){{document.getElementById('aiTrainBg').style.display='none';}}
(function(){{
  var hdr=document.getElementById('aiHeader');
  var win=document.getElementById('aiWindow');
  if(!hdr||!win) return;
  hdr.addEventListener('mousedown',function(e){{
    if(e.target.tagName==='BUTTON') return;
    aiDragging=true;
    aiDragX=e.clientX-win.offsetLeft;
    aiDragY=e.clientY-win.offsetTop;
    e.preventDefault();
  }});
  document.addEventListener('mousemove',function(e){{
    if(!aiDragging) return;
    win.style.left=(e.clientX-aiDragX)+'px';
    win.style.top=(e.clientY-aiDragY)+'px';
    win.style.right='auto';win.style.bottom='auto';
  }});
  document.addEventListener('mouseup',function(){{aiDragging=false;}});
}})();
function askAI(){{
  var inp=document.getElementById('aiInput');
  var q=inp.value.trim();if(!q) return;
  inp.value='';
  addAIMsg(q,'user');
  addAIMsg('...','ai');
  fetch('/api/ai/ask',{{method:'POST',headers:{{'Content-Type':'application/json','X-CSRF-Token':'{get_csrf_token()}'}},
    body:JSON.stringify({{question:q}})}}).then(r=>r.json()).then(d=>{{
    var msgs=document.getElementById('aiMessages');
    var answer=d.answer||'Javob topilmadi';
    // Timer tekshiruvi
    var timerMatch=answer.match(/\|\|TIMER:(\d+)\|\|/);
    if(timerMatch){{
      var ms=parseInt(timerMatch[1]);
      answer=answer.replace(/\|\|TIMER:\d+\|\|/,'');
      setTimeout(function(){{
        if(Notification.permission==='granted'){{new Notification('⏰ AI Eslatma',{{body:'Vaqt tugadi!'}});}}
        else{{alert('⏰ Eslatma: Vaqt tugadi!');}}
        addAIMsg('⏰ **Eslatma!** Siz belgilagan vaqt tugadi!','ai');
      }},ms);
      if(Notification.permission==='default')Notification.requestPermission();
    }}
    msgs.lastChild.innerHTML=formatAIMsg(answer);
    window._lastAIAnswer=answer;
  }}).catch(()=>{{
    var msgs=document.getElementById('aiMessages');
    msgs.lastChild.innerHTML='<span style="color:#f05d5d">Xato yuz berdi</span>';
  }});
}}
// ── Ovozli o'qish (TTS) ──
var _ttsEnabled=localStorage.getItem('ai_tts')==='1';
function speakLastAI(){{
  var text=window._lastAIAnswer||'';
  if(!text){{alert('Avval savol bering');return;}}
  // HTML teglarni tozalash
  var clean=text.replace(/<[^>]+>/g,'').replace(/\*\*/g,'').replace(/[=!@#~_`|]/g,'').replace(/\\n/g,' ');
  if(!('speechSynthesis' in window)){{alert('Brauzeringiz ovozli o\\'qishni qo\\'llab-quvvatlamaydi');return;}}
  window.speechSynthesis.cancel();
  var utter=new SpeechSynthesisUtterance(clean);
  utter.lang='uz';utter.rate=0.9;utter.pitch=1;
  // O'zbek tili topilmasa ingliz yoki rus
  var voices=window.speechSynthesis.getVoices();
  var uzVoice=voices.find(function(v){{return v.lang.startsWith('uz');}});
  if(uzVoice) utter.voice=uzVoice;
  else{{var ruVoice=voices.find(function(v){{return v.lang.startsWith('ru');}});if(ruVoice)utter.voice=ruVoice;}}
  window.speechSynthesis.speak(utter);
}}
function addAIMsg(text,role){{
  var msgs=document.getElementById('aiMessages');
  var div=document.createElement('div');
  div.style.cssText=role==='user'?'align-self:flex-end;background:#7c6fff22;border:1px solid #7c6fff44;border-radius:10px 10px 2px 10px;padding:8px 12px;max-width:85%;color:#d4daf0;font-size:.82rem':'align-self:flex-start;background:#0d0f18;border:1px solid #252d45;border-radius:10px 10px 10px 2px;padding:8px 12px;max-width:85%;color:#d4daf0;font-size:.82rem';
  div.innerHTML=role==='user'?text:formatAIMsg(text);
  msgs.appendChild(div);
  msgs.scrollTop=msgs.scrollHeight;
}}
function formatAIMsg(t){{
  // Rasmlar
  t=t.replace(/<img\s+([^>]*)>/gi,'<img $1 style="max-width:100%;border-radius:6px;margin:4px 0">');
  // ```code block```
  t=t.replace(/```([^`]+)```/g,'<pre style="background:#0d0f18;border:1px solid #252d45;border-radius:6px;padding:8px;margin:4px 0;overflow-x:auto;font-size:.78rem">$1</pre>');
  // **bold** qalin
  t=t.replace(/\*\*([^*]+)\*\*/g,'<b style="color:#fff">$1</b>');
  // *italic* kursiv
  t=t.replace(/\*([^*]+)\*/g,'<i>$1</i>');
  // __tagiga chiziq__
  t=t.replace(/__([^_]+)__/g,'<u style="text-decoration-color:#7c6fff">$1</u>');
  // ~~ustiga chiziq~~
  t=t.replace(/~~([^~]+)~~/g,'<s style="color:#5c6890">$1</s>');
  // ==sariq marker==
  t=t.replace(/==([^=]+)==/g,'<mark style="background:#f5c518;color:#000;padding:0 3px;border-radius:2px">$1</mark>');
  // !!qizil muhim!!
  t=t.replace(/!!([^!]+)!!/g,'<span style="color:#f05d5d;font-weight:700">$1</span>');
  // @@yashil muvaffaqiyat@@
  t=t.replace(/@@([^@]+)@@/g,'<span style="color:#22d3a0;font-weight:600">$1</span>');
  // ##ko'k havola rangi##
  t=t.replace(/##([^#]+)##/g,'<span style="color:#60a5fa">$1</span>');
  // `code` inline kod
  t=t.replace(/`([^`]+)`/g,'<code style="background:#252d45;padding:1px 5px;border-radius:3px;font-size:.8rem">$1</code>');
  // [havola](url)
  t=t.replace(/\[([^\]]+)\]\(([^)]+)\)/g,'<a href="$2" target="_blank" style="color:#7c6fff;text-decoration:underline">$1</a>');
  // yangi qator
  t=t.replace(/\\n/g,'<br>');
  // --- ajratuvchi chiziq
  t=t.replace(/^---$/gm,'<hr style="border:none;border-top:1px solid #252d45;margin:6px 0">');
  // > iqtibos
  t=t.replace(/^&gt;\s?(.+)/gm,'<blockquote style="border-left:3px solid #7c6fff;padding-left:8px;color:#8890b0;margin:4px 0">$1</blockquote>');
  // • bullet points
  t=t.replace(/• /g,'<span style="color:#7c6fff">•</span> ');
  // Raqamli ro'yxat: 1. 2. 3.
  t=t.replace(/^(\d+)\.\s/gm,'<span style="color:#22d3a0;font-weight:700">$1.</span> ');
  return t;
}}
function trainAI(type){{
  var payload={{}};
  if(type==='badword'){{
    var w=document.getElementById('aiBadWord').value.trim();
    var r=document.getElementById('aiBadResp').value.trim();
    if(!w&&!r){{alert('So\\'z yoki javob kiriting');return;}}
    payload={{type:'badword',word:w,response:r}};
  }}else if(type==='word'){{
    var w=document.getElementById('aiNewWord').value.trim();
    if(!w){{alert('So\\'z kiriting');return;}}
    payload={{type:'word',word:w}};
  }}else if(type==='topic'){{
    var t=document.getElementById('aiTopicName').value.trim();
    var info=document.getElementById('aiTopicInfo').value.trim();
    if(!t||!info){{alert('Mavzu va ma\\'lumot majburiy!');return;}}
    payload={{type:'topic',topic:t,info:info}};
  }}else{{
    var q=document.getElementById('aiTrainQ').value.trim();
    var a=document.getElementById('aiTrainA').value.trim();
    var cat=document.getElementById('aiTrainCat').value.trim();
    if(!q||!a){{alert('Savol va javob majburiy!');return;}}
    payload={{type:'qa',question:q,answer:a,category:cat}};
  }}
  fetch('/api/ai/train',{{method:'POST',headers:{{'Content-Type':'application/json','X-CSRF-Token':'{get_csrf_token()}'}},
    body:JSON.stringify(payload)}}).then(r=>r.json()).then(d=>{{
    if(d.ok){{
      if(type==='badword'){{document.getElementById('aiBadWord').value='';}}
      else if(type==='word')document.getElementById('aiNewWord').value='';
      else if(type==='topic'){{document.getElementById('aiTopicName').value='';document.getElementById('aiTopicInfo').value='';}}
      else{{document.getElementById('aiTrainQ').value='';document.getElementById('aiTrainA').value='';document.getElementById('aiTrainCat').value='';}}
      loadAIKnowledge();alert('✓ Saqlandi!');
    }}else alert('✗ '+(d.error||'Xato'));
  }});
}}
function showAITab(tab){{
  ['qa','topic','word','badword'].forEach(function(t){{
    var panel=document.getElementById('aiPanel'+t.charAt(0).toUpperCase()+t.slice(1));
    if(panel) panel.style.display=t===tab?'block':'none';
    var btn=document.getElementById('aiTab'+t.toUpperCase());
    if(btn){{btn.style.background=t===tab?'#7c6fff':'#252d45';btn.style.color=t===tab?'#fff':'#5c6890';}}
  }});
}}
function loadAIKnowledge(){{
  fetch('/api/ai/knowledge').then(r=>r.json()).then(d=>{{
    var list=document.getElementById('aiKnowledgeList');
    var html='';
    // Savol so'zlari
    if(d.words&&d.words.length){{
      html+='<div style="padding:4px 8px"><span style="color:#f5c518;font-size:.7rem;font-weight:600">SAVOL SO\\'ZLARI:</span> ';
      d.words.forEach(function(w){{html+='<span style="display:inline-block;background:#252d45;border-radius:4px;padding:2px 6px;margin:2px;font-size:.72rem;color:#d4daf0">'+w+' <span onclick="delAIWord(\\''+w+'\\')" style="color:#f05d5d;cursor:pointer;margin-left:3px">x</span></span>';}});
      html+='</div>';
    }}
    // Mavzular
    if(d.topics&&d.topics.length){{
      html+='<div style="padding:4px 8px;border-top:1px solid #1c2136;margin-top:4px"><span style="color:#22d3a0;font-size:.7rem;font-weight:600">MAVZULAR:</span></div>';
      d.topics.forEach(function(t){{
        html+='<div style="padding:4px 10px;border-bottom:1px solid #1c2136;font-size:.76rem;display:flex;gap:6px;align-items:center"><span style="color:#22d3a0;font-weight:600">'+t.topic+'</span><span style="color:#5c6890;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">'+t.info.slice(0,50)+'</span><button onclick="delAITopic('+t.id+')" style="background:transparent;border:none;color:#f05d5d;cursor:pointer;font-size:.72rem">🗑</button></div>';
      }});
    }}
    // Savol-javoblar
    (d.items||[]).forEach(function(it){{
      html+='<div style="padding:4px 10px;border-bottom:1px solid #1c2136;font-size:.76rem;display:flex;gap:6px;align-items:center"><span style="color:#7c6fff;flex:1">'+it.question+'</span><span style="color:#5c6890;font-size:.66rem">'+(it.category||'')+'</span><button onclick="deleteAIItem('+it.id+')" style="background:transparent;border:none;color:#f05d5d;cursor:pointer;font-size:.72rem">🗑</button></div>';
    }});
    list.innerHTML=html||'<p style="padding:12px;color:#5c6890;text-align:center;font-size:.78rem">Hali ma\\'lumot yoq</p>';
    // Savol so'zlari tabini ham yangilash
    var wl=document.getElementById('aiWordsList');
    if(wl&&d.words){{wl.innerHTML=d.words.map(function(w){{return '<span style="background:#252d45;border-radius:4px;padding:3px 8px;font-size:.76rem;color:#d4daf0">'+w+'</span>';}}).join('');}}
    // Badwords tabini yangilash
    var bl=document.getElementById('aiBadList');
    if(bl&&d.badwords){{bl.innerHTML=d.badwords.map(function(w){{return '<span style="background:#3b1010;border:1px solid #5c1a1a;border-radius:4px;padding:3px 8px;font-size:.74rem;color:#f05d5d">'+w+' <span onclick="delAIBad(\\''+w+'\\')" style="cursor:pointer;margin-left:3px">x</span></span>';}}).join('');}}
    if(d.badword_response){{var ri=document.getElementById('aiBadResp');if(ri&&!ri.value)ri.placeholder='Joriy: '+d.badword_response;}}
  }});
}}
function deleteAIItem(id){{
  fetch('/api/ai/knowledge/'+id,{{method:'DELETE',headers:{{'X-CSRF-Token':'{get_csrf_token()}'}}}}).then(()=>loadAIKnowledge());
}}
function delAITopic(id){{
  fetch('/api/ai/topics/'+id,{{method:'DELETE',headers:{{'X-CSRF-Token':'{get_csrf_token()}'}}}}).then(()=>loadAIKnowledge());
}}
function delAIWord(w){{
  fetch('/api/ai/words/'+encodeURIComponent(w),{{method:'DELETE',headers:{{'X-CSRF-Token':'{get_csrf_token()}'}}}}).then(()=>loadAIKnowledge());
}}
function delAIBad(w){{
  fetch('/api/ai/badwords/'+encodeURIComponent(w),{{method:'DELETE',headers:{{'X-CSRF-Token':'{get_csrf_token()}'}}}}).then(()=>loadAIKnowledge());
}}
</script>
</body></html>"""

def _auth_pg(title, body, flash=None, ftype="er"):
    fl = f'<div class="al al-{ftype}">{flash}</div>' if flash else ""
    return f"""<!DOCTYPE html>
<html lang="uz"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} — SrvManager</title>
<style>{CSS}
.aw{{display:flex;align-items:center;justify-content:center;min-height:100vh;padding:20px}}
.ab{{background:var(--card);border:1px solid var(--brd);border-radius:14px;
  padding:32px;width:100%;max-width:360px}}
</style></head><body>
<div class="aw"><div class="ab">
  <p style="text-align:center;font-size:2rem;margin-bottom:8px">⬡</p>
  <h2 style="text-align:center;color:#fff;margin-bottom:3px;font-size:1.1rem">SrvManager</h2>
  <p style="text-align:center;color:var(--mt);font-size:.8rem;margin-bottom:20px">{title}</p>
  {fl}{body}
</div></div></body></html>"""

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     AUTH                                                  ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/login", methods=["GET","POST"])
def login():
    ip = get_ip()
    if is_blocked(ip): abort(403)
    err = None
    if request.method == "POST":
        u = request.form.get("username","").strip()
        p = request.form.get("password","")
        user = q1("SELECT * FROM users WHERE username=? AND is_active=1", (u,))
        if user and check_password_hash(user["password_hash"], p):
            clear_fails(ip)
            session.permanent = True
            session.update({"user_id":user["id"],"username":user["username"],
                            "role":user["role"],"admin":user["role"]=="admin"})
            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            db_exec("UPDATE users SET last_login=? WHERE id=?", (now, user["id"]), fetch=False)
            telegram_send(f"✅ Yangi kirish\nFoydalanuvchi: {user['username']}\nIP: {ip}")
            return redirect("/dashboard")
        else:
            if record_fail(ip, u):
                return _auth_pg("Kirish","",f"Juda ko'p xato. {CFG['BAN_MINUTES']} daqiqa bloklandi."), 403
            err = "Noto'g'ri login yoki parol"
    f = """
    <form method="POST">
      <div class="fld"><label>Login</label><input name="username" required placeholder="admin" autocomplete="username"></div>
      <div class="fld"><label>Parol</label><input name="password" type="password" required autocomplete="current-password"></div>
      <button class="btn bp" style="width:100%">Kirish</button>
    </form>
    <p style="text-align:center;margin-top:12px;font-size:.8rem">
      Hisob yo'qmi? <a href="/register">Ro'yxatdan o'tish</a></p>"""
    return _auth_pg("Kirish", f, err)

@app.route("/register", methods=["GET","POST"])
def register():
    if is_blocked(get_ip()): abort(403)
    err = suc = None
    if request.method == "POST":
        u = request.form.get("username","").strip()
        e = request.form.get("email","").strip()
        p = request.form.get("password","")
        c = request.form.get("confirm","")
        if len(u)<3: err="Username kamida 3 ta belgi"
        elif len(p)<6: err="Parol kamida 6 ta belgi"
        elif p!=c: err="Parollar mos kelmadi"
        else:
            try:
                db_exec("INSERT INTO users (username,email,password_hash) VALUES (?,?,?)",
                        (u, e, generate_password_hash(p)), fetch=False)
                suc = "Ro'yxatdan o'tildi! Kirishingiz mumkin."
                telegram_send(f"🆕 Yangi foydalanuvchi ro'yxatdan o'tdi: {u} ({e})")
            except: err="Bu username yoki email allaqachon mavjud"
    f = """
    <form method="POST">
      <div class="fld"><label>Username</label><input name="username" required></div>
      <div class="fld"><label>Email</label><input name="email" type="email" required></div>
      <div class="fld"><label>Parol</label><input name="password" type="password" required></div>
      <div class="fld"><label>Tasdiqlash</label><input name="confirm" type="password" required></div>
      <button class="btn bp" style="width:100%">Ro'yxatdan o'tish</button>
    </form>
    <p style="text-align:center;margin-top:12px;font-size:.8rem"><a href="/login">← Kirish</a></p>"""
    return _auth_pg("Ro'yxatdan o'tish", f, suc or err, "ok" if suc else "er")

@app.route("/logout")
def logout():
    session.clear(); return redirect("/login")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                           DASHBOARD                                       ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/")
@app.route("/dashboard")
@user_req
def dashboard():
    def cnt(t): return (q1(f"SELECT COUNT(*) c FROM {t}") or {}).get("c",0)
    s = {"links":cnt("links WHERE is_active=1"),"files":cnt("files"),
         "projs":cnt("projects"),"visits":cnt("access_logs WHERE date(visited_at)=date('now')")}
    logs = db_exec("SELECT mode,ip_address,path,status_code,visited_at FROM access_logs ORDER BY visited_at DESC LIMIT 10") or []
    lr = "".join(f"""<tr>
      <td><span class="bx xp">{l['mode']}</span></td>
      <td><code style="font-size:.75rem">{l['ip_address']}</code></td>
      <td style="max-width:180px;overflow:hidden;text-overflow:ellipsis;font-size:.77rem">{l['path']}</td>
      <td><span class="bx {'xg' if l['status_code']==200 else 'xr'}">{l['status_code']}</span></td>
      <td class="tm" style="font-size:.75rem">{str(l['visited_at'])[:16]}</td>
    </tr>""" for l in logs)
    modes_html = ""
    for mode,icon,desc in [("private","🔒","Maxsus token havolasi"),("lan","📡","WiFi tarmog'i"),("global","🌍","Internet / ngrok")]:
        on = mode_on(mode)
        modes_html += f"""
        <div class="card" style="border-left:3px solid {'var(--gr)' if on else 'var(--rd)'}">
          <div class="fl"><span style="font-size:1.3rem">{icon}</span>
            <b style="color:#fff">{mode.upper()}</b>
            <span class="bx {'xg' if on else 'xr'} mla">{'Faol' if on else "O'chiq"}</span></div>
          <p class="tm mt" style="font-size:.78rem">{desc}</p>
        </div>"""
    body = f"""
    <div class="g g4 mb" style="margin-bottom:18px">
      <div class="stat"><div class="v">{s['links']}</div><div class="l">Havolalar</div></div>
      <div class="stat"><div class="v">{s['files']}</div><div class="l">Fayllar</div></div>
      <div class="stat"><div class="v">{s['projs']}</div><div class="l">Loyihalar</div></div>
      <div class="stat"><div class="v">{s['visits']}</div><div class="l">Bugungi tashriflar</div></div>
    </div>
    <div class="g g3 mb">{modes_html}</div>
    <div class="card"><h3>So'nggi tashriflar</h3>
      <div class="tw"><table><thead><tr>
        <th>Rejim</th><th>IP</th><th>Yo'l</th><th>Status</th><th>Vaqt</th>
      </tr></thead><tbody>{lr or '<tr><td colspan=5 style="text-align:center;color:var(--mt);padding:16px">Hali tashrif yo\'q</td></tr>'}</tbody></table></div>
    </div>"""
    return _pg("Dashboard", body, "dash")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     REJIMLAR BOSHQARUVI                                  ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/modes")
@user_req
def modes_page():
    ip=local_ip(); ssid=get_ssid(); port=CFG["PORT"]
    pub=_active_mode.get("url","") or "(ngrok ishga tushirilmagan)"
    data=[("private","🔒","Shaxsiy","Token — faqat siz",f"http://127.0.0.1:{port}/p/TOKEN"),
          ("lan","📡","LAN","WiFi — "+ssid,f"http://{ip}:{port}"),
          ("global","🌍","Global","Internet orqali",pub)]
    cards=""
    for mode,icon,label,desc,url in data:
        on=mode_on(mode)
        ngrok_btns=""
        if mode=="global":
            ngrok_btns='<form method="POST" action="/modes/ngrok/start" style="display:inline">'+csrf_field()+'<button class="btn bgh bsm">🚀 Ngrok start</button></form>'
            if _active_mode.get("url"):
                ngrok_btns+='<form method="POST" action="/modes/ngrok/stop" style="display:inline;margin-left:6px">'+csrf_field()+'<button class="btn br bsm">⏹ Stop</button></form>'
        safe_url=url.replace("'","")
        cards+=f"""
        <div class="mcard {'on' if on else ''}">
          <div class="fl mb"><span style="font-size:1.4rem">{icon}</span>
            <b style="color:#fff">{label}</b>
            <span class="bx {'xg' if on else 'xr'} mla">{'Faol' if on else "O'chiq"}</span></div>
          <p class="tm" style="font-size:.79rem;margin-bottom:10px">{desc}</p>
          <div class="urlbox">{url}</div>
          <button class="cpb mt" onclick="copyText('{safe_url}')">Nusxa</button>
          <div class="fl mt">
            <form method="POST" action="/modes/toggle/{mode}">{csrf_field()}
              <button class="btn {'br' if on else 'bg'} bsm">{'🔴 O\'chir' if on else '🟢 Yoq'}</button>
            </form>
            {ngrok_btns}
          </div>
        </div>"""
    srv_on = server_enabled()
    srv_btn = ""
    if session.get("admin"):
        srv_btn = f"""<form method="POST" action="/admin/server/toggle" class="mt">{csrf_field()}
          <button class="btn {'br' if srv_on else 'bg'} bsm">{"🔴 Serverni o'chirish" if srv_on else "🟢 Serverni yoqish"}</button>
        </form>"""
    srv_card = f"""
    <div class="card mb" style="border-left:3px solid {'var(--gr)' if srv_on else 'var(--rd)'}">
      <div class="fl"><span style="font-size:1.4rem">{'🟢' if srv_on else '🔴'}</span>
        <b style="color:#fff">SERVER (umumiy kirish)</b>
        <span class="bx {'xg' if srv_on else 'xr'} mla">{'Yoqilgan' if srv_on else "O'chirilgan"}</span></div>
      <p class="tm mt" style="font-size:.79rem">Bu tugma butun saytga (barcha rejimlar uchun) kirishni yoqadi yoki o'chiradi.
      O'chirilganda faqat admin tizimga kirib qayta yoqishi mumkin — jarayon ishlab turaveradi, faqat tashqi kirish to'xtaydi.</p>
      {srv_btn}
    </div>"""
    guest_on = get_setting("require_login","1") == "0"
    guest_btn = ""
    if session.get("admin"):
        guest_btn = f"""<form method="POST" action="/admin/guest/toggle" class="mt">{csrf_field()}
          <button class="btn {'br' if guest_on else 'bgh'} bsm">{"🔴 Guest rejimini o'chirish" if guest_on else "🟢 Guest rejimini yoqish"}</button>
        </form>"""
    guest_card = f"""
    <div class="card mb" style="border-left:3px solid {'var(--yl)' if guest_on else 'var(--brd)'}">
      <div class="fl"><span style="font-size:1.4rem">👤</span>
        <b style="color:#fff">LOGINSIZ KIRISH (Guest)</b>
        <span class="bx {'xy' if guest_on else 'xm'} mla">{'Yoqilgan' if guest_on else "O'chirilgan"}</span></div>
      <p class="tm mt" style="font-size:.79rem">⚠️ Yoqilsa, saytga kirgan HAR KIM login qilmasdan barcha fayl/loyihalarni
      ko'rishi va tahrirlashi mumkin bo'ladi (guest=viewer rolida). Faqat <b>private</b> rejimda, ishonchli tarmoqda yoqing.</p>
      {guest_btn}
    </div>"""
    body=f"""
    <div class="fl mb"><h2 style="color:#fff">Rejimlar</h2>
      <a href="/links/new" class="btn bp mla">+ Havola yaratish</a></div>
    {srv_card}
    {guest_card}
    <div class="g g3">{cards}</div>
    <div class="card mt"><h3>Tarmoq ma'lumotlari</h3>
      <div class="g g3">
        <div><p class="tm mb" style="font-size:.78rem">Lokal IP</p>
          <code style="color:var(--ac)">{ip}:{port}</code></div>
        <div><p class="tm mb" style="font-size:.78rem">WiFi SSID</p>
          <code style="color:var(--ac)">{ssid}</code></div>
        <div><p class="tm mb" style="font-size:.78rem">Ngrok URL</p>
          <code style="color:var(--gr)">{_active_mode.get('url') or 'Ishga tushirilmagan'}</code></div>
      </div>
    </div>"""
    return _pg("Rejimlar", body, "modes")

@app.route("/modes/toggle/<mode>", methods=["POST"])
@user_req
def toggle_mode(mode):
    if mode not in ("private","lan","global"): abort(400)
    r=q1("SELECT is_enabled FROM mode_settings WHERE mode=?",(mode,))
    db_exec("UPDATE mode_settings SET is_enabled=? WHERE mode=?",
            (0 if r and r["is_enabled"] else 1, mode), fetch=False)
    return redirect("/modes")

@app.route("/modes/ngrok/start", methods=["POST"])
@user_req
def ngrok_start():
    global _ngrok_tunnel
    if not NGROK_OK: return redirect("/modes")
    try:
        if CFG["NGROK_TOKEN"]: _ngrok.set_auth_token(CFG["NGROK_TOKEN"])
        _ngrok_tunnel=_ngrok.connect(CFG["PORT"],"http")
        _active_mode["url"]=_ngrok_tunnel.public_url
    except Exception as e:
        print(_c(f"[ngrok] {e}",R))
    return redirect("/modes")

@app.route("/modes/ngrok/stop", methods=["POST"])
@user_req
def ngrok_stop():
    global _ngrok_tunnel
    if NGROK_OK:
        try: _ngrok.kill()
        except: pass
    _ngrok_tunnel=None; _active_mode["url"]=None
    return redirect("/modes")

@app.route("/admin/guest/toggle", methods=["POST"])
@admin_req
def admin_guest_toggle():
    cur = get_setting("require_login", "1")
    set_setting("require_login", "1" if cur == "0" else "0")
    return redirect(request.referrer or "/modes")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     HAVOLALAR                                             ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/links")
@user_req
def links_list():
    uid=session["user_id"]; adm=session.get("admin") or session.get("_guest")
    if adm:
        lks=db_exec("SELECT l.*,u.username FROM links l LEFT JOIN users u ON l.owner_id=u.id ORDER BY l.created_at DESC") or []
    else:
        lks=db_exec("SELECT l.*,u.username FROM links l LEFT JOIN users u ON l.owner_id=u.id WHERE l.owner_id=? ORDER BY l.created_at DESC",(uid,)) or []
    port=CFG["PORT"]; rows=""
    for lk in lks:
        mb={"private":"xp","lan":"xb","global":"xg"}.get(lk["mode"],"xm")
        stat='<span class="bx xg">Faol</span>' if lk["is_active"] else '<span class="bx xr">O\'chiq</span>'
        exp=str(lk["expires_at"])[:16] if lk.get("expires_at") else "∞"
        url=f"http://127.0.0.1:{port}/p/{lk['token']}"
        pw="🔐 " if lk.get("password_hash") else ""
        rows+=f"""<tr>
          <td><span class="bx {mb}">{lk['mode']}</span></td>
          <td>{pw}{lk.get('label') or '—'}</td>
          <td><code style="font-size:.72rem;color:var(--ac)">{lk['token'][:14]}...</code>
            <button class="cpb" onclick="copyText('{url}')">Nusxa</button></td>
          <td>{stat}</td><td>{lk['visit_count']}</td><td>{exp}</td>
          <td>{lk.get('username') or '—'}</td>
          <td class="fl">
            <a href="/qr/{lk['token']}" target="_blank" class="btn bgh bsm" title="QR-kod">📱</a>
            <a href="/links/edit/{lk['id']}" class="btn bgh bsm">✏️</a>
            <form method="POST" action="/links/toggle/{lk['id']}">{csrf_field()}
              <button class="btn bgh bsm">{'⏸' if lk['is_active'] else '▶️'}</button></form>
            <form method="POST" action="/links/delete/{lk['id']}" onsubmit="return confirm('O\\'chirish?')">{csrf_field()}
              <button class="btn br bsm">🗑</button></form>
          </td>
        </tr>"""
    body=f"""
    <div class="fl mb"><h2 style="color:#fff">Havolalar</h2>
      <a href="/links/new" class="btn bp mla">+ Yangi havola</a></div>
    <div class="card" style="padding:0"><div class="tw">
      <table><thead><tr>
        <th>Rejim</th><th>Nom</th><th>Token</th><th>Holat</th>
        <th>Tashriflar</th><th>Muddat</th><th>Egasi</th><th>Amallar</th>
      </tr></thead><tbody>{rows or '<tr><td colspan=8 style="text-align:center;color:var(--mt);padding:20px">Hali havola yo\'q</td></tr>'}</tbody></table>
    </div></div>"""
    return _pg("Havolalar", body, "links")

@app.route("/links/new", methods=["GET","POST"])
@app.route("/links/edit/<int:lid>", methods=["GET","POST"])
@user_req
@write_req
def link_form(lid=None):
    lk={}
    if lid: lk=q1("SELECT * FROM links WHERE id=?",(lid,)) or {}
    err=suc=None
    if request.method=="POST":
        mode=request.form.get("mode","private"); label=request.form.get("label","")
        tgt=request.form.get("target_path",""); pw=request.form.get("password","")
        exp=request.form.get("expires",""); pid=request.form.get("project_id","") or None
        ph=generate_password_hash(pw) if pw else None
        edt=None
        if exp:
            try: edt=datetime.strptime(exp,"%Y-%m-%dT%H:%M").strftime("%Y-%m-%d %H:%M:%S")
            except: err="Noto'g'ri sana formati"
        if not err:
            if lid:
                if ph:
                    db_exec("UPDATE links SET mode=?,label=?,target_path=?,password_hash=?,expires_at=?,project_id=? WHERE id=?",
                            (mode,label,tgt,ph,edt,pid,lid),fetch=False)
                else:
                    db_exec("UPDATE links SET mode=?,label=?,target_path=?,expires_at=?,project_id=? WHERE id=?",
                            (mode,label,tgt,edt,pid,lid),fetch=False)
                suc="Havola yangilandi"
            else:
                tok=gtok()
                db_exec("INSERT INTO links (token,mode,label,target_path,password_hash,expires_at,owner_id,project_id)"
                        " VALUES (?,?,?,?,?,?,?,?)",
                        (tok,mode,label,tgt,ph,edt,session["user_id"],pid),fetch=False)
                return redirect("/links")
    projs=db_exec("SELECT id,name FROM projects WHERE owner_id=? ORDER BY name",(session["user_id"],)) or []
    po="".join(f'<option value="{p["id"]}" {"selected" if lk.get("project_id")==p["id"] else ""}>{p["name"]}</option>' for p in projs)
    mo="".join(f'<option value="{m}" {"selected" if lk.get("mode",m)==m else ""}>{m.upper()}</option>' for m in ["private","lan","global"])
    form=f"""
    {'<div class="al al-er">'+err+'</div>' if err else ''}
    {'<div class="al al-ok">'+suc+'</div>' if suc else ''}
    <form method="POST">{csrf_field()}
      <div class="g g2">
        <div class="fld"><label>Rejim</label><select name="mode">{mo}</select></div>
        <div class="fld"><label>Nom</label><input name="label" value="{lk.get('label','') or ''}"></div>
      </div>
      <div class="fld"><label>Maqsad URL / yo'l</label>
        <input name="target_path" value="{lk.get('target_path','') or ''}" placeholder="/download/uuid yoki https://..."></div>
      <div class="g g2">
        <div class="fld"><label>Parol himoyasi (bo'sh = yo'q)</label>
          <input name="password" type="password" placeholder="Yangi parol..."></div>
        <div class="fld"><label>Muddati</label>
          <input name="expires" type="datetime-local" value="{str(lk.get('expires_at',''))[:16] if lk.get('expires_at') else ''}"></div>
      </div>
      <div class="fld"><label>Loyiha (ixtiyoriy)</label>
        <select name="project_id"><option value="">— Tanlang —</option>{po}</select></div>
      <button class="btn bp">{'Yangilash' if lid else 'Yaratish'}</button>
      <a href="/links" class="btn bgh" style="margin-left:8px">Bekor</a>
    </form>"""
    return _pg("Havola",f'<div class="card"><h3>{"Havola tahrirlash" if lid else "Yangi havola"}</h3>{form}</div>',"links")

@app.route("/links/toggle/<int:lid>", methods=["POST"])
@user_req
@write_req
def link_toggle(lid):
    db_exec("UPDATE links SET is_active=1-is_active WHERE id=?",(lid,),fetch=False)
    return redirect("/links")

@app.route("/links/delete/<int:lid>", methods=["POST"])
@user_req
@write_req
def link_delete(lid):
    db_exec("DELETE FROM links WHERE id=?",(lid,),fetch=False)
    return redirect("/links")

@app.route("/p/<token>", methods=["GET","POST"])
def link_access(token):
    ip=get_ip()
    if is_blocked(ip): abort(403)
    pw=request.form.get("password") if request.method=="POST" else None
    lk,err=check_link(token,pw)
    if err=="NEED_PASSWORD":
        return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
        <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh}}</style>
        </head><body>
        <div style="background:var(--card);border:1px solid var(--brd);border-radius:12px;padding:28px;max-width:320px;width:100%">
          <p style="font-size:1.6rem;margin-bottom:10px">🔐</p>
          <h2 style="color:#fff;margin-bottom:4px;font-size:1rem">Parol kerak</h2>
          <p class="tm" style="font-size:.8rem;margin-bottom:16px">Himoyalangan havola</p>
          <form method="POST">
            <div class="fld"><input name="password" type="password" placeholder="Parol..." required autofocus></div>
            <button class="btn bp" style="width:100%">Kirish</button>
          </form>
        </div></body></html>"""
    if err:
        log_access("private",token,403)
        return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
        <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center}}</style>
        </head><body><div><p style="font-size:2.5rem">🚫</p>
        <h2 style="color:var(--rd);margin:10px 0">{err}</h2>
        <a href="/" class="btn bgh">← Asosiy</a></div></body></html>""",403
    db_exec("UPDATE links SET visit_count=visit_count+1 WHERE token=?",(token,),fetch=False)
    log_access(lk["mode"],token)
    tgt=lk.get("target_path",""); pid=lk.get("project_id")
    if pid:
        pr=q1("SELECT uuid FROM projects WHERE id=?",(pid,))
        if pr: return redirect(f"/preview/{pr['uuid']}?token={token}")
    if tgt:
        if tgt.startswith("http"): return redirect(tgt)
        return redirect(tgt)
    return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
    <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center}}</style>
    </head><body><div><p style="font-size:2.5rem">✅</p>
    <h2 style="color:var(--gr);margin:10px 0">Havola faol!</h2>
    <p class="tm">Token: <code>{token[:12]}...</code></p></div></body></html>"""

# ── QR-kod ────────────────────────────────────────────────
@app.route("/qr/<token>")
def qr_image(token):
    if not QRCODE_OK:
        return "QR-kod uchun kerak: pip install qrcode[pil]", 501
    port=CFG["PORT"]; ip=local_ip()
    scope = request.args.get("scope","lan")   # private | lan | global
    if scope=="private":
        url=f"http://127.0.0.1:{port}/p/{token}"
    elif scope=="global" and _active_mode.get("url"):
        url=f"{_active_mode['url']}/p/{token}"
    else:
        url=f"http://{ip}:{port}/p/{token}"
    img = qrcode.make(url)
    buf = io.BytesIO(); img.save(buf, format="PNG"); buf.seek(0)
    return Response(buf.getvalue(), mimetype="image/png")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     FAYLLAR                                               ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/files")
@user_req
def files_list():
    uid=session["user_id"]; adm=session.get("admin") or session.get("_guest")
    if adm:
        fs=db_exec("SELECT f.*,u.username FROM files f LEFT JOIN users u ON f.owner_id=u.id ORDER BY f.created_at DESC") or []
    else:
        fs=db_exec("SELECT f.*,u.username FROM files f LEFT JOIN users u ON f.owner_id=u.id WHERE f.owner_id=? ORDER BY f.created_at DESC",(uid,)) or []
    rows=""
    for f in fs:
        pub='<span class="bx xg">Ommaviy</span>' if f["is_public"] else '<span class="bx xm">Shaxsiy</span>'
        exp=str(f["expires_at"])[:16] if f.get("expires_at") else "∞"
        rows+=f"""<tr>
          <td>{f['original_name']}</td>
          <td><span class="bx xb">{f.get('file_type','?')}</span></td>
          <td>{hsize(f.get('file_size_bytes',0))}</td>
          <td>{pub}</td><td>{f['download_count']}</td><td>{exp}</td>
          <td>{f.get('username') or '—'}</td>
          <td class="fl">
            <a href="/download/{f['uuid']}" class="btn bg bsm">⬇ Olish</a>
            <form method="POST" action="/files/delete/{f['uuid']}" onsubmit="return confirm('O\\'chirish?')">{csrf_field()}
              <button class="btn br bsm">🗑</button></form>
          </td>
        </tr>"""
    body=f"""
    <div class="fl mb"><h2 style="color:#fff">Fayllar</h2></div>
    <div class="card"><h3>Fayl yuklash (max {CFG['MAX_FILE_MB']} MB)</h3>
      <form method="POST" action="/files/upload" enctype="multipart/form-data">{csrf_field()}
        <div class="row">
          <div class="fld" style="flex:1"><label>Fayl</label>
            <input type="file" name="file" required></div>
          <div class="fld"><label>Muddati (ixtiyoriy)</label>
            <input type="datetime-local" name="expires"></div>
          <div class="fld"><label>&nbsp;</label>
            <label style="display:flex;align-items:center;gap:6px;color:var(--mt);cursor:pointer">
              <input type="checkbox" name="is_public" style="width:auto">Ommaviy</label></div>
        </div>
        <button class="btn bp">⬆ Yuklash</button>
      </form>
    </div>
    <div class="card" style="padding:0"><div class="tw">
      <table><thead><tr>
        <th>Nomi</th><th>Tur</th><th>Hajm</th><th>Holat</th>
        <th>Yuklab olish</th><th>Muddat</th><th>Egasi</th><th>Amallar</th>
      </tr></thead><tbody>{rows or '<tr><td colspan=8 style="text-align:center;color:var(--mt);padding:20px">Hali fayl yo\'q</td></tr>'}</tbody></table>
    </div></div>"""
    return _pg("Fayllar",body,"files")

@app.route("/files/upload",methods=["POST"])
@user_req
@write_req
def file_upload():
    f=request.files.get("file")
    if not f or not f.filename: return redirect("/files")
    if not allowed(f.filename):
        return _pg("Fayllar",'<div class="al al-er">Ruxsat etilmagan fayl turi!</div>',"files")
    f.seek(0,2); sz=f.tell(); f.seek(0)
    if sz>CFG["MAX_FILE_MB"]*1024*1024:
        return _pg("Fayllar",f'<div class="al al-er">Fayl {CFG["MAX_FILE_MB"]}MB dan katta!</div>',"files")
    uid_s=str(uuid.uuid4()); safe=secure_filename(f.filename)
    ext=Path(safe).suffix.lower(); stored=uid_s+ext
    f.save(str(FILES_PATH/stored))
    edt=None
    exp=request.form.get("expires","")
    if exp:
        try: edt=datetime.strptime(exp,"%Y-%m-%dT%H:%M").strftime("%Y-%m-%d %H:%M:%S")
        except: pass
    pub=1 if request.form.get("is_public") else 0
    db_exec("INSERT INTO files (uuid,original_name,stored_name,file_type,file_size_bytes,owner_id,is_public,expires_at)"
            " VALUES (?,?,?,?,?,?,?,?)",
            (uid_s,safe,stored,ext.lstrip("."),sz,session["user_id"],pub,edt),fetch=False)
    telegram_send(f"📁 Yangi fayl yuklandi: {safe} ({hsize(sz)})\nYuklovchi: {session.get('username')}")
    return redirect("/files")

@app.route("/download/<fuid>")
def file_download(fuid):
    row=q1("SELECT * FROM files WHERE uuid=?",(fuid,))
    if not row: abort(404)
    if row.get("expires_at"):
        try:
            if datetime.now()>datetime.strptime(row["expires_at"],"%Y-%m-%d %H:%M:%S"): abort(410)
        except: pass
    if not row["is_public"] and session.get("user_id")!=row["owner_id"] and not session.get("admin"):
        return redirect("/login")
    dest=FILES_PATH/row["stored_name"]
    if not dest.exists(): abort(404)
    db_exec("UPDATE files SET download_count=download_count+1 WHERE uuid=?",(fuid,),fetch=False)
    nb=dest.stat().st_size
    log_access("private",path=f"/download/{fuid}",nb=nb)
    return send_from_directory(str(FILES_PATH),row["stored_name"],
                               as_attachment=True,download_name=row["original_name"])

@app.route("/files/delete/<fuid>",methods=["POST"])
@user_req
@write_req
def file_delete(fuid):
    row=q1("SELECT * FROM files WHERE uuid=?",(fuid,))
    if row:
        d=FILES_PATH/row["stored_name"]
        if d.exists(): d.unlink()
        db_exec("DELETE FROM files WHERE uuid=?",(fuid,),fetch=False)
    return redirect("/files")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║              KOD MUHARRIRI (CodeMirror) + LOYIHALAR + PREVIEW            ║
# ║   Qo'shimchalar: autosave, Quick Open, global qidiruv/almashtirish,      ║
# ║   drag&drop, linting, auto-import, user snippets, versiya tarixi,        ║
# ║   split-view, konsol paneli, rasm/SVG preview, format-on-save,           ║
# ║   mini-xarita, breadcrumb — va Emmet uchun ikki marta Tab muammosi tuzatildi║
# ╚══════════════════════════════════════════════════════════════════════════╝
EDITOR_TMPL = """<!DOCTYPE html>
<html lang="uz"><head><meta charset="UTF-8">
<title>Muharrir — NAME</title>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/codemirror.min.css">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/theme/dracula.min.css">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/hint/show-hint.min.css">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/lint/lint.min.css">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/dialog/dialog.min.css">
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/codemirror.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/mode/htmlmixed/htmlmixed.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/mode/xml/xml.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/mode/css/css.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/mode/javascript/javascript.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/edit/matchbrackets.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/edit/closebrackets.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/selection/active-line.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/comment/comment.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/hint/show-hint.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/search/searchcursor.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/dialog/dialog.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/lint/lint.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/jshint/2.13.6/jshint.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.65.16/addon/lint/javascript-lint.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/js-beautify/1.15.1/beautify.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/js-beautify/1.15.1/beautify-css.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/js-beautify/1.15.1/beautify-html.min.js"></script>
<style>
INSERTCSS
body{overflow:hidden;height:100vh;display:flex;flex-direction:column}
.eh{background:var(--surf);border-bottom:1px solid var(--brd);padding:9px 14px;
  display:flex;align-items:center;gap:9px;flex-shrink:0;flex-wrap:wrap}
.eh h1{font-size:.9rem;font-weight:700;color:#fff;margin-right:auto}
.crumb{font-size:.72rem;color:var(--mt);background:var(--surf);border-bottom:1px solid var(--brd);
  padding:5px 14px;flex-shrink:0}
.crumb b{color:var(--ac);font-weight:600}
.ebMain{display:flex;flex:1;overflow:hidden}
#sidebar{width:210px;flex-shrink:0;background:var(--surf);border-right:1px solid var(--brd);
  display:flex;flex-direction:column;overflow:hidden}
.sbhead{padding:8px 10px;display:flex;gap:6px;border-bottom:1px solid var(--brd);flex-wrap:wrap}
.sbhead button{flex:1;background:transparent;border:1px solid var(--brd);color:var(--mt);
  border-radius:6px;padding:4px;cursor:pointer;font-size:.72rem}
.sbhead button:hover{border-color:var(--ac);color:var(--ac)}
#fileTree{flex:1;overflow-y:auto;padding:6px 0}
.frow{display:flex;align-items:center;gap:6px;padding:5px 10px;font-size:.78rem;
  color:var(--tx);cursor:pointer;white-space:nowrap;border-left:2px solid transparent}
.frow:hover{background:rgba(124,111,255,.08)}
.frow.act{background:rgba(124,111,255,.14);border-left-color:var(--ac);color:#fff}
.frow.dragover{outline:1px dashed var(--ac);background:rgba(124,111,255,.18)}
.fic{font-size:.85rem}
#codePane{display:flex;flex-direction:column;flex:0 0 45%;border-right:1px solid var(--brd);min-width:220px}
.tabsBar{display:flex;background:var(--surf);border-bottom:1px solid var(--brd);overflow-x:auto;flex-shrink:0}
.ftab{display:flex;align-items:center;gap:8px;padding:7px 10px;font-size:.78rem;color:var(--mt);
  cursor:pointer;border-right:1px solid var(--brd);white-space:nowrap}
.ftab.act{color:#fff;background:rgba(124,111,255,.08);border-bottom:2px solid var(--ac)}
.ftabx{opacity:.6;padding:0 2px}
.ftabx:hover{opacity:1;color:var(--rd)}
.editWrap{flex:1;display:flex;overflow:hidden}
#cmHost{flex:1;overflow:hidden}
#cmHost2{flex:1;overflow:hidden;border-left:1px solid var(--brd);display:none}
#minimap{width:56px;flex-shrink:0;background:#0a0c14;border-left:1px solid var(--brd);cursor:pointer}
#cmHost .CodeMirror,#cmHost2 .CodeMirror{height:100%;font-size:13px;background:#0d0f18}
.CodeMirror-matchingbracket{color:#22d3a0 !important;font-weight:700;text-decoration:underline;text-decoration-color:#22d3a0}
.CodeMirror-nonmatchingbracket{color:#f05d5d !important;font-weight:700}
.CodeMirror-activeline-background{background:rgba(124,111,255,.06)}
.CodeMirror-hints{background:#161929;border:1px solid #252d45;color:#d4daf0;
  font-family:'Consolas',monospace;font-size:12.5px;box-shadow:0 8px 24px rgba(0,0,0,.45);
  border-radius:8px;padding:4px 0;z-index:99999}
.CodeMirror-hint{padding:5px 12px;border-radius:0}
li.CodeMirror-hint-active{background:#7c6fff !important;color:#fff !important}
.cm-hint-snip{color:#22d3a0;font-size:10px;margin-left:10px;opacity:.85}
.CodeMirror-dialog{background:var(--surf);color:var(--tx);border-bottom:1px solid var(--brd)}
.CodeMirror-lint-marker-error{color:var(--rd)} .CodeMirror-lint-marker-warning{color:var(--yl)}
.CodeMirror-lint-tooltip{background:#161929;border:1px solid #252d45;color:var(--tx);
  border-radius:6px;font-size:12px;padding:4px 8px;z-index:999999}
#resizer{width:6px;cursor:col-resize;background:var(--brd);flex-shrink:0}
#resizer:hover{background:var(--ac)}
.pvcol{flex:1;display:flex;flex-direction:column;min-width:220px}
.devbar{display:flex;align-items:center;gap:6px;padding:7px 12px;background:var(--surf);
  border-bottom:1px solid var(--brd);font-size:.76rem;flex-shrink:0;flex-wrap:wrap}
.devbar button{background:transparent;border:1px solid var(--brd);color:var(--mt);
  border-radius:6px;padding:4px 9px;cursor:pointer;font-size:.74rem}
.devbar button:hover,.devbar button.on{border-color:var(--ac);color:var(--ac)}
.pvwrap{flex:1;display:flex;align-items:center;justify-content:center;overflow:auto;background:#05060a}
.pvwrap iframe{border:none}
.pvwrap.desktop iframe{width:100%;height:100%}
.pvwrap.tablet iframe{width:768px;height:1024px;max-width:94%;max-height:94%;
  border:10px solid #2b2f3a;border-radius:16px;background:#fff}
.pvwrap.mobile iframe{width:375px;height:667px;max-width:90%;max-height:94%;
  border:10px solid #2b2f3a;border-radius:26px;background:#fff}
.khint{font-size:.68rem;color:var(--mt);cursor:help}
#ctxMenu{position:fixed;display:none;background:#161929;border:1px solid #252d45;border-radius:8px;
  padding:4px 0;z-index:999999;min-width:180px;box-shadow:0 8px 24px rgba(0,0,0,.5)}
#ctxMenu div{padding:7px 14px;font-size:.8rem;color:var(--tx);cursor:pointer}
#ctxMenu div:hover{background:rgba(124,111,255,.15)}
.modalBg{position:fixed;inset:0;background:rgba(0,0,0,.55);display:none;
  align-items:flex-start;justify-content:center;z-index:9999999;padding-top:8vh}
.modalBox{background:var(--card);border:1px solid var(--brd);border-radius:12px;
  width:92%;max-width:560px;max-height:78vh;display:flex;flex-direction:column;overflow:hidden}
.modalBox input[type=text]{width:100%;padding:10px 14px;background:var(--bg);border:none;
  border-bottom:1px solid var(--brd);color:var(--tx);font-size:.9rem;outline:none}
.modalList{overflow-y:auto;flex:1}
.modalRow{padding:9px 14px;font-size:.82rem;color:var(--tx);cursor:pointer;
  display:flex;justify-content:space-between;gap:8px}
.modalRow:hover,.modalRow.sel{background:rgba(124,111,255,.14)}
.modalRow small{color:var(--mt)}
#consolePanel{height:130px;flex-shrink:0;background:#05060a;border-top:1px solid var(--brd);
  overflow-y:auto;font-family:monospace;font-size:.74rem;display:none}
#consolePanel .cline{padding:3px 10px;border-bottom:1px solid #12141f;white-space:pre-wrap;word-break:break-all}
#consolePanel .clog{color:var(--tx)} #consolePanel .cerr{color:var(--rd)} #consolePanel .cwarn{color:var(--yl)}
.histItem{padding:8px 12px;font-size:.78rem;border-bottom:1px solid var(--brd);display:flex;justify-content:space-between;gap:8px}
.histItem button{flex-shrink:0}
@media(max-width:768px){.layout{flex-direction:column}.sb{width:100%;height:auto;position:static}}
</style></head><body>
<div class="eh">
  <h1>✏️ NAME</h1>
  <span class="khint" id="autosaveInd" title="Avtosaqlash holati">💾 —</span>
  <button class="btn bp bsm" onclick="runCode()" title="Ctrl+Enter">▶ Run</button>
  <button class="btn bg bsm" onclick="saveActive()" title="Ctrl+S">💾 Saqlash</button>
  <button class="btn bgh bsm" onclick="formatActive()" title="Shift+Alt+F">🧹 Formatlash</button>
  <label class="khint" style="cursor:pointer"><input type="checkbox" id="fmtOnSave" style="width:auto;vertical-align:middle"> Saqlashda formatlash</label>
  <button class="btn bgh bsm" onclick="openQuickOpen()" title="Ctrl+P">📂 Quick Open</button>
  <button class="btn bgh bsm" onclick="openGlobalSearch()" title="Ctrl+Shift+F">🔍 Global qidiruv</button>
  <button class="btn bgh bsm" onclick="toggleSplit()">⊞ Split</button>
  <button class="btn bgh bsm" onclick="toggleConsole()">🖥 Konsol</button>
  <button class="btn bgh bsm" onclick="openSnippets()">✨ Snippetlar</button>
  <button class="btn bgh bsm" onclick="openHistory()">🕘 Tarix</button>
  <button class="btn bgh bsm" onclick="openBackendPanel()">🐍 Backend</button>
  <button class="btn bgh bsm" onclick="openHelpPanel()">❓ Yordam</button>
  <button class="btn bgh bsm" onclick="openChatPanel()">💬 Chat</button>
  <button class="btn bgh bsm" onclick="openTodoPanel()">🎯 TODO</button>
  <button class="btn bgh bsm" onclick="openComponentsPanel()">🧩 Komponent</button>
  <button class="btn bgh bsm" onclick="openColorPicker()">📐 Rang</button>
  <button class="btn bgh bsm" onclick="openTerminal()">💻 Terminal</button>
  <button class="btn bgh bsm" onclick="generatePWA()">📱 PWA</button>
  <button class="btn bgh bsm" onclick="generateReadme()">📑 README</button>
  <a href="/projects/download/UUID" class="btn bgh bsm">⬇ ZIP</a>
  <span class="khint" title="Emmet: div.foo#bar, ul>li*3, div+p, (div>p)*2, a{Matn} kabi qisqartmalarni yozib Tab yoki Enter bosing&#10;CSS: w100%, h50vh, m10-20, p0, df, jcc, aic, fxd, tac kabi qisqartmalar ham qo'llab-quvvatlanadi&#10;Ctrl+Space — takliflar ro'yxati&#10;Ctrl+P — Quick Open&#10;Ctrl+Shift+F — global qidiruv&#10;Ctrl+S — saqlash&#10;Ctrl+Enter — ishga tushirish&#10;Ctrl+/ — izohga olish&#10;Shift+Alt+F — formatlash&#10;Alt+Click — qo'shimcha kursor (multi-cursor)&#10;O'ng tugma — fayl daraxtida yangi fayl/papka/nomini o'zgartirish/o'chirish&#10;Sudrab tashlash — faylni boshqa papkaga ko'chirish">⌨ Tugmalar</span>
  <a href="/projects" class="btn bgh bsm">← Loyihalar</a>
  <a href="/preview/UUID" target="_blank" class="btn bgh bsm">👁 To'liq</a>
</div>
<div class="crumb" id="breadcrumb">—</div>
<div class="ebMain" id="ebMain">
  <aside id="sidebar" oncontextmenu="event.preventDefault();contextTargetPath=null;openCtxMenu(event,null);">
    <div class="sbhead">
      <button onclick="contextTargetPath=null;ctxNewFile()">+📄 Fayl</button>
      <button onclick="contextTargetPath=null;ctxNewFolder()">+📁 Papka</button>
    </div>
    <div id="fileTree"></div>
  </aside>
  <div id="codePane">
    <div class="tabsBar" id="tabsBar"></div>
    <div class="editWrap">
      <div id="cmHost"></div>
      <div id="cmHost2"></div>
      <canvas id="minimap" width="56" height="600"></canvas>
    </div>
  </div>
  <div id="resizer"></div>
  <div class="pvcol">
    <div class="devbar">
      <button onclick="setDevice('desktop')" id="devDesktop">🖥 Desktop</button>
      <button onclick="setDevice('tablet')" id="devTablet">📱 Planshet</button>
      <button onclick="setDevice('mobile')" id="devMobile">📱 Telefon</button>
      <button onclick="toggleFullscreen()">⛶ Kattalashtirish</button>
      <span id="ps" style="margin-left:auto;color:var(--gr)">✓ Tayyor</span>
    </div>
    <div class="pvwrap desktop" id="pvwrap">
      <iframe id="pf" sandbox="allow-scripts allow-same-origin allow-forms allow-popups"></iframe>
    </div>
    <div id="consolePanel"></div>
  </div>
</div>
<div id="ctxMenu">
  <div onclick="ctxNewFile()">📄 Yangi fayl</div>
  <div onclick="ctxNewFolder()">📁 Yangi papka</div>
  <div onclick="ctxRename()">✏️ Nomini o'zgartirish</div>
  <div onclick="ctxDelete()">🗑 O'chirish</div>
</div>

<div class="modalBg" id="quickOpenBg"><div class="modalBox">
  <input type="text" id="quickOpenInput" placeholder="Fayl qidirish... (Ctrl+P)">
  <div class="modalList" id="quickOpenList"></div>
</div></div>

<div class="modalBg" id="globalSearchBg"><div class="modalBox" style="max-width:680px">
  <input type="text" id="gsQuery" placeholder="Barcha fayllarda qidirish...">
  <input type="text" id="gsReplace" placeholder="Almashtirish matni (ixtiyoriy)">
  <div class="fl" style="padding:8px 14px">
    <button class="btn bp bsm" onclick="runGlobalSearch()">🔍 Qidirish</button>
    <button class="btn br bsm" onclick="runGlobalReplace()">🔁 Barchasini almashtirish</button>
    <button class="btn bgh bsm mla" onclick="closeModal('globalSearchBg')">Yopish</button>
  </div>
  <div class="modalList" id="gsResults"></div>
</div></div>

<div class="modalBg" id="helpBg"><div class="modalBox" style="max-width:720px;max-height:85vh">
  <div style="padding:12px 14px;border-bottom:1px solid var(--brd);display:flex;align-items:center;justify-content:space-between">
    <b style="color:#fff">❓ Emmet qisqartmalari va klaviatura tugmalari</b>
    <button class="btn bgh bsm" onclick="closeModal('helpBg')">✕</button>
  </div>
  <div class="modalList" style="padding:14px;overflow-y:auto;font-size:.82rem;line-height:1.7">

    <h3 style="color:var(--ac);margin-bottom:8px">⌨️ Klaviatura tugmalari</h3>
    <table style="width:100%;margin-bottom:18px"><tbody>
      <tr><td style="color:var(--gr);width:180px"><kbd>Tab</kbd></td><td>Emmet/Snippet kengaytirish</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Ctrl+S</kbd></td><td>Saqlash</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Ctrl+Enter</kbd></td><td>Ishga tushirish (Run)</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Ctrl+Space</kbd></td><td>Takliflar ro'yxati (Autocomplete)</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Ctrl+P</kbd></td><td>Quick Open — fayl qidirish</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Ctrl+Shift+F</kbd></td><td>Global qidiruv / almashtirish</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Ctrl+/</kbd></td><td>Izohga olish / izohdan chiqarish</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Shift+Alt+F</kbd></td><td>Kodni formatlash (beautify)</td></tr>
      <tr><td style="color:var(--gr)"><kbd>Alt+Click</kbd></td><td>Ko'p kursor (multi-cursor)</td></tr>
    </tbody></table>

    <h3 style="color:var(--ac);margin-bottom:8px">🌐 HTML Emmet qisqartmalari</h3>
    <p style="color:var(--mt);margin-bottom:8px">Qisqartmani yozib <kbd>Tab</kbd> yoki <kbd>Enter</kbd> bosing:</p>
    <table style="width:100%;margin-bottom:18px"><tbody>
      <tr><td style="color:var(--yl);width:200px"><code>!</code></td><td>HTML5 to'liq shablon (boilerplate)</td></tr>
      <tr><td style="color:var(--yl)"><code>div.box#main</code></td><td>&lt;div class="box" id="main"&gt;&lt;/div&gt;</td></tr>
      <tr><td style="color:var(--yl)"><code>ul>li*5</code></td><td>ul ichida 5 ta li elementi</td></tr>
      <tr><td style="color:var(--yl)"><code>nav>ul>li*4>a</code></td><td>Navigatsiya tuzilmasi</td></tr>
      <tr><td style="color:var(--yl)"><code>div+p+span</code></td><td>Bir xil darajada 3 ta element</td></tr>
      <tr><td style="color:var(--yl)"><code>(div>p)*3</code></td><td>Guruhni 3 marta takrorlash</td></tr>
      <tr><td style="color:var(--yl)"><code>a[href=#]{Havola}</code></td><td>Atributli va matnli element</td></tr>
      <tr><td style="color:var(--yl)"><code>div.item$*4</code></td><td>item1, item2, item3, item4 klasslar</td></tr>
      <tr><td style="color:var(--yl)"><code>lorem</code> / <code>lorem30</code></td><td>Lorem ipsum matn (30 so'z)</td></tr>
      <tr><td style="color:var(--yl)"><code>img</code></td><td>&lt;img src="" alt=""&gt;</td></tr>
      <tr><td style="color:var(--yl)"><code>input</code></td><td>&lt;input type="text"&gt;</td></tr>
      <tr><td style="color:var(--yl)"><code>link</code></td><td>&lt;link rel="stylesheet" href=""&gt;</td></tr>
      <tr><td style="color:var(--yl)"><code>html5</code> / <code>com</code></td><td>HTML5 shablon / izoh bloki</td></tr>
    </tbody></table>

    <h3 style="color:var(--ac);margin-bottom:8px">🎨 CSS Emmet qisqartmalari</h3>
    <p style="color:var(--mt);margin-bottom:8px">CSS faylda qisqartmani yozib <kbd>Tab</kbd> bosing:</p>
    <table style="width:100%;margin-bottom:18px"><tbody>
      <tr><td style="color:var(--yl);width:200px"><code>w100%</code></td><td>width: 100%;</td></tr>
      <tr><td style="color:var(--yl)"><code>h50vh</code></td><td>height: 50vh;</td></tr>
      <tr><td style="color:var(--yl)"><code>m10</code> / <code>m10-20</code></td><td>margin: 10px; / margin: 10px 20px;</td></tr>
      <tr><td style="color:var(--yl)"><code>p0</code></td><td>padding: 0;</td></tr>
      <tr><td style="color:var(--yl)"><code>mt15</code> / <code>mb20</code></td><td>margin-top: 15px; / margin-bottom: 20px;</td></tr>
      <tr><td style="color:var(--yl)"><code>fs16</code></td><td>font-size: 16px;</td></tr>
      <tr><td style="color:var(--yl)"><code>fw700</code></td><td>font-weight: 700;</td></tr>
      <tr><td style="color:var(--yl)"><code>lh1.5</code></td><td>line-height: 1.5;</td></tr>
      <tr><td style="color:var(--yl)"><code>df</code> / <code>flex</code></td><td>display: flex;</td></tr>
      <tr><td style="color:var(--yl)"><code>dg</code> / <code>grid</code></td><td>display: grid;</td></tr>
      <tr><td style="color:var(--yl)"><code>jcc</code></td><td>justify-content: center;</td></tr>
      <tr><td style="color:var(--yl)"><code>aic</code></td><td>align-items: center;</td></tr>
      <tr><td style="color:var(--yl)"><code>fxd</code> / <code>fxdc</code></td><td>flex-direction: column;</td></tr>
      <tr><td style="color:var(--yl)"><code>fxww</code></td><td>flex-wrap: wrap;</td></tr>
      <tr><td style="color:var(--yl)"><code>center</code></td><td>display:flex; align-items:center; justify-content:center;</td></tr>
      <tr><td style="color:var(--yl)"><code>tac</code></td><td>text-align: center;</td></tr>
      <tr><td style="color:var(--yl)"><code>brr</code></td><td>border-radius:;</td></tr>
      <tr><td style="color:var(--yl)"><code>op</code></td><td>opacity:;</td></tr>
      <tr><td style="color:var(--yl)"><code>cur</code></td><td>cursor: pointer;</td></tr>
      <tr><td style="color:var(--yl)"><code>trs</code></td><td>transition:;</td></tr>
    </tbody></table>

    <h3 style="color:var(--ac);margin-bottom:8px">📜 JavaScript Snippet qisqartmalari</h3>
    <table style="width:100%;margin-bottom:18px"><tbody>
      <tr><td style="color:var(--yl);width:200px"><code>fn</code></td><td>function nomi() { }</td></tr>
      <tr><td style="color:var(--yl)"><code>af</code> / <code>anfn</code></td><td>() => { } (arrow function)</td></tr>
      <tr><td style="color:var(--yl)"><code>cl</code> / <code>clg</code></td><td>console.log();</td></tr>
      <tr><td style="color:var(--yl)"><code>ce</code></td><td>console.error();</td></tr>
      <tr><td style="color:var(--yl)"><code>fori</code></td><td>for (let i = 0; i < .length; i++)</td></tr>
      <tr><td style="color:var(--yl)"><code>forof</code></td><td>for (const item of ...)</td></tr>
      <tr><td style="color:var(--yl)"><code>fe</code></td><td>.forEach(item => { })</td></tr>
      <tr><td style="color:var(--yl)"><code>asf</code></td><td>async function() { }</td></tr>
      <tr><td style="color:var(--yl)"><code>awt</code></td><td>await ...;</td></tr>
      <tr><td style="color:var(--yl)"><code>qs</code></td><td>document.querySelector('');</td></tr>
      <tr><td style="color:var(--yl)"><code>qsa</code></td><td>document.querySelectorAll('');</td></tr>
      <tr><td style="color:var(--yl)"><code>addE</code></td><td>addEventListener('', () => { });</td></tr>
      <tr><td style="color:var(--yl)"><code>setT</code> / <code>sto</code></td><td>setTimeout(() => { }, 1000);</td></tr>
      <tr><td style="color:var(--yl)"><code>imp</code></td><td>import ... from '';</td></tr>
      <tr><td style="color:var(--yl)"><code>exp</code></td><td>export default ...;</td></tr>
      <tr><td style="color:var(--yl)"><code>ifj</code></td><td>if (...) { }</td></tr>
    </tbody></table>

    <h3 style="color:var(--ac);margin-bottom:8px">🖱️ Muharrir imkoniyatlari</h3>
    <table style="width:100%"><tbody>
      <tr><td style="color:var(--gr);width:200px">Fayl daraxti</td><td>O'ng tugma — yangi fayl/papka, nom o'zgartirish, o'chirish</td></tr>
      <tr><td style="color:var(--gr)">Sudrab tashlash</td><td>Faylni boshqa papkaga ko'chirish (drag & drop)</td></tr>
      <tr><td style="color:var(--gr)">Split view</td><td>⊞ Split tugmasi — ikki panelda bir vaqtda ishlash</td></tr>
      <tr><td style="color:var(--gr)">Konsol</td><td>console.log() natijalarini ko'rish (🖥 Konsol)</td></tr>
      <tr><td style="color:var(--gr)">Snippetlar</td><td>Shaxsiy qisqartmalar yaratish (✨ Snippetlar)</td></tr>
      <tr><td style="color:var(--gr)">Tarix</td><td>Har saqlashda avtomatik snapshot — eski holatni tiklash</td></tr>
      <tr><td style="color:var(--gr)">Formatlash</td><td>Shift+Alt+F yoki "Saqlashda formatlash" checkbox</td></tr>
      <tr><td style="color:var(--gr)">Backend</td><td>Loyiha ichidagi Python serverless funksiyalar</td></tr>
    </tbody></table>

  </div>
</div></div>

<div class="modalBg" id="chatBg"><div class="modalBox" style="max-width:480px;height:70vh">
  <div style="padding:10px 14px;border-bottom:1px solid var(--brd);display:flex;align-items:center;justify-content:space-between">
    <b style="color:#fff">💬 Loyiha chati</b>
    <button class="btn bgh bsm" onclick="closeModal('chatBg')">✕</button></div>
  <div id="chatMessages" style="flex:1;overflow-y:auto;padding:10px;font-size:.82rem"></div>
  <div style="padding:8px 14px;border-top:1px solid var(--brd);display:flex;gap:6px">
    <input type="text" id="chatInput" placeholder="Xabar yozing..." style="flex:1;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem" onkeydown="if(event.key==='Enter')sendChat()">
    <button class="btn bp bsm" onclick="sendChat()">↑</button>
  </div>
</div></div>

<div class="modalBg" id="todoBg"><div class="modalBox" style="max-width:500px">
  <div style="padding:10px 14px;border-bottom:1px solid var(--brd);display:flex;align-items:center;justify-content:space-between">
    <b style="color:#fff">🎯 TODO / Vazifalar</b>
    <button class="btn bgh bsm" onclick="closeModal('todoBg')">✕</button></div>
  <div style="padding:10px 14px;display:flex;gap:6px">
    <input type="text" id="todoInput" placeholder="Yangi vazifa..." style="flex:1;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem" onkeydown="if(event.key==='Enter')addTodo()">
    <select id="todoPriority" style="padding:5px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.78rem"><option value="normal">Normal</option><option value="high">Yuqori</option><option value="low">Past</option></select>
    <button class="btn bp bsm" onclick="addTodo()">+</button>
  </div>
  <div class="modalList" id="todoList" style="max-height:50vh;overflow-y:auto"></div>
</div></div>

<div class="modalBg" id="compBg"><div class="modalBox" style="max-width:700px;max-height:80vh">
  <div style="padding:10px 14px;border-bottom:1px solid var(--brd);display:flex;align-items:center;justify-content:space-between">
    <b style="color:#fff">🧩 Komponent kutubxonasi</b>
    <button class="btn bgh bsm" onclick="closeModal('compBg')">✕</button></div>
  <div class="modalList" id="compList" style="overflow-y:auto"></div>
</div></div>

<div class="modalBg" id="colorBg"><div class="modalBox" style="max-width:420px">
  <div style="padding:10px 14px;border-bottom:1px solid var(--brd);display:flex;align-items:center;justify-content:space-between">
    <b style="color:#fff">📐 Color Picker</b>
    <button class="btn bgh bsm" onclick="closeModal('colorBg')">✕</button></div>
  <div style="padding:14px">
    <input type="color" id="colorPickerInput" value="#7c6fff" style="width:100%;height:40px;border:none;cursor:pointer;border-radius:6px">
    <div style="margin-top:8px;display:flex;gap:6px;align-items:center">
      <input type="text" id="colorHexVal" value="#7c6fff" style="flex:1;padding:6px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-family:monospace;font-size:.85rem">
      <button class="btn bp bsm" onclick="insertColor()">Qo'shish</button>
    </div>
    <div id="colorPalettes" style="margin-top:12px"></div>
  </div>
</div></div>

<div class="modalBg" id="termBg"><div class="modalBox" style="max-width:700px;height:70vh">
  <div style="padding:10px 14px;border-bottom:1px solid var(--brd);display:flex;align-items:center;justify-content:space-between">
    <b style="color:#fff">💻 Terminal</b>
    <button class="btn bgh bsm" onclick="closeModal('termBg')">✕</button></div>
  <div id="termOutput" style="flex:1;overflow-y:auto;padding:10px;font-family:monospace;font-size:.78rem;background:#05060a;color:var(--gr);white-space:pre-wrap"></div>
  <div style="padding:8px 14px;border-top:1px solid var(--brd);display:flex;gap:6px">
    <span style="color:var(--gr);font-family:monospace;font-size:.82rem">$</span>
    <input type="text" id="termInput" placeholder="Buyruq kiriting..." style="flex:1;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-family:monospace;font-size:.82rem" onkeydown="if(event.key==='Enter')runTermCmd()">
    <button class="btn bp bsm" onclick="runTermCmd()">▶</button>
  </div>
</div></div>

<div class="modalBg" id="snippetsBg"><div class="modalBox">
  <div style="padding:12px 14px;border-bottom:1px solid var(--brd)"><b style="color:#fff">✨ Mening snippetlarim</b></div>
  <div style="padding:12px 14px">
    <div class="g g3">
      <select id="snpLang"><option value="h">HTML</option><option value="c">CSS</option><option value="j">JS</option></select>
      <input type="text" id="snpTrigger" placeholder="Trigger (masalan: mycard)">
      <button class="btn bp bsm" onclick="addSnippet()">+ Qo'shish</button>
    </div>
    <textarea id="snpBody" placeholder="Kod (kursor o'rni uchun § belgisidan foydalaning)" style="width:100%;min-height:70px;margin-top:8px;background:var(--bg);border:1px solid var(--brd);color:var(--tx);border-radius:7px;padding:8px"></textarea>
  </div>
  <div class="modalList" id="snpList"></div>
  <div style="padding:10px 14px"><button class="btn bgh bsm" onclick="closeModal('snippetsBg')">Yopish</button></div>
</div></div>

<div class="modalBg" id="backendBg"><div class="modalBox" style="max-width:640px">
  <div style="padding:12px 14px;border-bottom:1px solid var(--brd)"><b style="color:#fff">🐍 Backend route'lari</b></div>
  <div style="padding:12px 14px">
    <div class="g g3">
      <select id="beMethod"><option>GET</option><option>POST</option><option>PUT</option><option>DELETE</option></select>
      <input type="text" id="bePath" placeholder="Yo'l (masalan: hello)">
      <button class="btn bp bsm" onclick="addBackendRoute()">+ Qo'shish</button>
    </div>
    <textarea id="beCode" placeholder="Python kod. Kirish: request, query, body. Natija: result = ..." style="width:100%;min-height:90px;margin-top:8px;background:var(--bg);border:1px solid var(--brd);color:var(--tx);border-radius:7px;padding:8px;font-family:monospace"></textarea>
    <p class="khint mt">Chaqiruv manzili: <code>/api/run/UUID/&lt;yo'l&gt;</code> — kirish: <code>request</code>, <code>query</code>, <code>body</code>; natijani <code>result</code> o'zgaruvchisiga yozing.</p>
  </div>
  <div class="modalList" id="beList"></div>
  <div style="padding:10px 14px"><button class="btn bgh bsm" onclick="closeModal('backendBg')">Yopish</button></div>
</div></div>

<div class="modalBg" id="historyBg"><div class="modalBox">
  <div style="padding:12px 14px;border-bottom:1px solid var(--brd)"><b style="color:#fff" id="histTitle">🕘 Versiya tarixi</b></div>
  <div class="modalList" id="histList"></div>
  <div style="padding:10px 14px"><button class="btn bgh bsm" onclick="closeModal('historyBg')">Yopish</button></div>
</div></div>

<script>
function debounce(fn,ms){var t;return function(){clearTimeout(t);t=setTimeout(fn,ms);};}
function flash(msg,color){
  var el=document.getElementById('ps'); if(!el) return;
  el.textContent=msg; el.style.color='var(--'+color+')';
}
function closeModal(id){ document.getElementById(id).style.display='none'; }
var CSRF_TOKEN = "CSRFTOKEN";
function authFetch(url, opts){
  opts = opts || {};
  opts.headers = Object.assign({'X-CSRF-Token': CSRF_TOKEN}, opts.headers||{});
  return fetch(url, opts);
}

/* ══════════════════════════════════════════════════════════════════════
   EMMET MOTORI — HTML va CSS qisqartmalarini to'liq kodga aylantiradi
   ══════════════════════════════════════════════════════════════════════ */
var activeTab='h';
var CURSOR_MARK = '\\u0001';

var HTML_VOID_TAGS = ['area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr'];
var HTML_TAG_WHITELIST = ['div','span','p','a','ul','ol','li','table','tr','td','th','thead','tbody','tfoot',
  'form','input','button','img','nav','section','article','header','footer','aside','h1','h2','h3','h4','h5','h6',
  'label','textarea','select','option','optgroup','i','b','strong','em','small','br','hr','iframe','video','audio',
  'canvas','svg','path','script','link','meta','style','title','head','body','html','main','figure','figcaption',
  'blockquote','code','pre','strike','u','sub','sup','dl','dt','dd','fieldset','legend','address','time','mark'];
var HTML_DEFAULT_ATTRS = {
  a: [['href','']],
  img: [['src',''],['alt','']],
  link: [['rel','stylesheet'],['href','']],
  input: [['type','text']],
  script: [['src','']]
};
var IMPLICIT_CHILD_TAG = {ul:'li', ol:'li', table:'tr', tbody:'tr', thead:'tr', tfoot:'tr', tr:'td', select:'option', optgroup:'option'};
var LOREM_WORDS = ('lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod tempor incididunt ut '+
  'labore et dolore magna aliqua ut enim ad minim veniam quis nostrud exercitation ullamco laboris nisi ut '+
  'aliquip ex ea commodo consequat duis aute irure dolor in reprehenderit voluptate velit esse cillum '+
  'dolore eu fugiat nulla pariatur excepteur sint occaecat cupidatat non proident sunt culpa qui officia '+
  'deserunt mollit anim id est laborum').split(' ');

function generateLorem(n){
  var out = [];
  for (var i=0;i<n;i++) out.push(LOREM_WORDS[i % LOREM_WORDS.length]);
  var s = out.join(' ');
  return s.charAt(0).toUpperCase() + s.slice(1) + '.';
}

function substDollar(s, index){
  if (s == null) return s;
  return s.replace(/\$+/g, function(m){ return String(index).padStart(m.length,'0'); });
}

function EmmetState(str){ return { s: str, i: 0, len: str.length }; }
function emParseTop(st){ return emParseSiblings(st); }

function emParseSiblings(st){
  var nodes = [emParseChain(st)];
  while (st.s[st.i] === '+') {
    st.i++;
    nodes.push(emParseChain(st));
  }
  while (st.s[st.i] === '^') {
    while (st.s[st.i] === '^') st.i++;
    if (st.i < st.len && st.s[st.i] !== ')') {
      nodes.push(emParseChain(st));
      while (st.s[st.i] === '+') { st.i++; nodes.push(emParseChain(st)); }
    }
  }
  return nodes;
}

function emParseChain(st){
  var node = emParsePrimary(st);
  if (st.s[st.i] === '>') {
    st.i++;
    node.children = emParseSiblings(st);
  }
  return node;
}

function emParsePrimary(st){
  if (st.s[st.i] === '(') {
    st.i++;
    var items = emParseSiblings(st);
    if (st.s[st.i] === ')') st.i++;
    var mult = emParseMultiplier(st);
    return {type:'group', items: items, mult: mult};
  }
  return emParseElement(st);
}

function emParseMultiplier(st){
  if (st.s[st.i] === '*') {
    st.i++;
    var n = '';
    while (st.i<st.len && /[0-9]/.test(st.s[st.i])) { n += st.s[st.i]; st.i++; }
    return parseInt(n||'1',10);
  }
  return 1;
}

function emParseElement(st){
  var s = st.s, len = st.len;
  var name = '';
  while (st.i<len && /[a-zA-Z0-9:_-]/.test(s[st.i])) { name += s[st.i]; st.i++; }
  var implicitName = false;
  if (!name) { name = 'div'; implicitName = true; }
  var classes = [], id = '', attrs = [], text = null;
  while (st.i < len) {
    var c = s[st.i];
    if (c === '.') {
      st.i++; var cls='';
      while (st.i<len && /[a-zA-Z0-9_-]/.test(s[st.i])) { cls+=s[st.i]; st.i++; }
      classes.push(cls);
    } else if (c === '#') {
      st.i++; var idv='';
      while (st.i<len && /[a-zA-Z0-9_-]/.test(s[st.i])) { idv+=s[st.i]; st.i++; }
      id = idv;
    } else if (c === '[') {
      st.i++; var inner='';
      while (st.i<len && s[st.i] !== ']') { inner+=s[st.i]; st.i++; }
      st.i++;
      var parts = inner.match(/[^\s"']+|"[^"]*"|'[^']*'/g) || [];
      for (var k=0;k<parts.length;k++){
        var p = parts[k], eq = p.indexOf('=');
        if (eq === -1) attrs.push({key:p, val:'', hasEq:false});
        else {
          var val = p.slice(eq+1).replace(/^["']|["']$/g,'');
          attrs.push({key:p.slice(0,eq), val: val, hasEq:true});
        }
      }
    } else if (c === '{') {
      st.i++; var t=''; var depth=1;
      while (st.i<len && depth>0) {
        if (s[st.i]==='{') depth++;
        else if (s[st.i]==='}') { depth--; if(depth===0){st.i++;break;} }
        t += s[st.i]; st.i++;
      }
      text = t;
    } else break;
  }
  var mult = emParseMultiplier(st);
  return {type:'element', name:name, implicitName:implicitName, classes:classes, id:id, attrs:attrs, text:text, mult:mult, children:null};
}

function emRenderNodes(nodes, indent, index, ctx, parentName){
  var lines = [];
  for (var n=0;n<nodes.length;n++){
    lines = lines.concat(emRenderNode(nodes[n], indent, index, ctx, parentName));
  }
  return lines;
}

function emRenderNode(node, indent, inheritedIndex, ctx, parentName){
  var mult = node.mult || 1;
  var lines = [];
  for (var i=1;i<=mult;i++){
    var idx = mult>1 ? i : inheritedIndex;
    if (node.type === 'group') {
      lines = lines.concat(emRenderNodes(node.items, indent, idx, ctx, parentName));
    } else {
      lines = lines.concat(emRenderElement(node, indent, idx, ctx, parentName));
    }
  }
  return lines;
}

function emRenderElement(node, indent, index, ctx, parentName){
  var pad = '  '.repeat(indent);
  if (/^lorem[0-9]*$/i.test(node.name)) {
    var n = parseInt(node.name.replace(/^lorem/i,''),10) || 30;
    return [pad + generateLorem(n)];
  }
  var tagName = node.name;
  if (node.implicitName && parentName && IMPLICIT_CHILD_TAG[parentName]) {
    tagName = IMPLICIT_CHILD_TAG[parentName];
  }
  var classes = node.classes.map(function(c){ return substDollar(c,index); });
  var id = node.id ? substDollar(node.id,index) : '';
  var attrsOut = '';
  if (classes.length) attrsOut += ' class="'+classes.join(' ')+'"';
  if (id) attrsOut += ' id="'+id+'"';
  var defaults = HTML_DEFAULT_ATTRS[tagName] || [];
  var explicitKeys = {};
  for (var a=0;a<node.attrs.length;a++) explicitKeys[node.attrs[a].key]=1;
  for (var d=0;d<defaults.length;d++){
    var dk=defaults[d][0], dv=defaults[d][1];
    if (!explicitKeys[dk]) attrsOut += ' '+dk+'="'+dv+'"';
  }
  for (var a2=0;a2<node.attrs.length;a2++){
    var at = node.attrs[a2];
    if (!at.hasEq) attrsOut += ' '+at.key;
    else attrsOut += ' '+at.key+'="'+substDollar(at.val,index)+'"';
  }
  var isVoid = HTML_VOID_TAGS.indexOf(tagName.toLowerCase()) !== -1;
  if (isVoid) return [pad+'<'+tagName+attrsOut+'>'];
  var text = node.text != null ? substDollar(node.text,index) : null;
  var children = node.children;
  if (children && children.length) {
    var out = [pad+'<'+tagName+attrsOut+'>'];
    out = out.concat(emRenderNodes(children, indent+1, index, ctx, tagName));
    out.push(pad+'</'+tagName+'>');
    return out;
  }
  if (text != null) {
    return [pad+'<'+tagName+attrsOut+'>'+text+'</'+tagName+'>'];
  }
  if (!ctx.placed) {
    ctx.placed = true;
    return [pad+'<'+tagName+attrsOut+'>'+CURSOR_MARK+'</'+tagName+'>'];
  }
  return [pad+'<'+tagName+attrsOut+'></'+tagName+'>'];
}

var HTML5_BOILERPLATE = '<!DOCTYPE html>\\n<html lang="uz">\\n<head>\\n  <meta charset="UTF-8">\\n  <title>'+CURSOR_MARK+'</title>\\n</head>\\n<body>\\n  \\n</body>\\n</html>';

function finalizeEmmetText(text){
  var idx = text.indexOf(CURSOR_MARK);
  if (idx>=0) return {text: text.slice(0,idx)+text.slice(idx+CURSOR_MARK.length), cursorOffset: idx};
  return {text:text, cursorOffset:text.length};
}

function expandEmmetHTML(abbr){
  abbr = (abbr||'').trim();
  if (!abbr) return null;
  if (abbr === '!') return finalizeEmmetText(HTML5_BOILERPLATE);
  if (/^lorem[0-9]*$/i.test(abbr)) {
    var nn = parseInt(abbr.replace(/^lorem/i,''),10) || 30;
    var txt = generateLorem(nn);
    return {text: txt, cursorOffset: txt.length};
  }
  var hasSpecial = /[.#\[\]{}*+>^()]/.test(abbr);
  var bareWord = /^[a-zA-Z][a-zA-Z0-9]*$/.test(abbr);
  if (!hasSpecial && bareWord && HTML_TAG_WHITELIST.indexOf(abbr.toLowerCase())===-1) return null;
  try {
    var st = EmmetState(abbr);
    var nodes = emParseTop(st);
    if (st.i < st.len) return null;
    var ctx = {placed:false};
    var lines = emRenderNodes(nodes, 0, 1, ctx, null);
    var text = lines.join('\\n');
    return finalizeEmmetText(text);
  } catch(e){ return null; }
}

/* Emmet naqshi ekanini tez aniqlash — hintni yopish qarorlari uchun */
function looksLikeEmmet(word){
  return /[.#\[\]{}*+>^()]/.test(word) || word === '!' || /^lorem[0-9]*$/i.test(word);
}

var CSS_PROP_PREFIXES = {
  minw:'min-width', minh:'min-height', maxw:'max-width', maxh:'max-height',
  mw:'max-width', mh:'max-height',
  mt:'margin-top', mb:'margin-bottom', ml:'margin-left', mr:'margin-right',
  pt:'padding-top', pb:'padding-bottom', pl:'padding-left', pr:'padding-right',
  m:'margin', p:'padding', w:'width', h:'height',
  fs:'font-size', fw:'font-weight', lh:'line-height', z:'z-index',
  brr:'border-radius', op:'opacity', top:'top', left:'left', right:'right', bottom:'bottom'
};
var CSS_VALUE_KEYWORDS = {a:'auto', n:'none', i:'inherit', s:'solid', h:'hidden', b:'both'};
var CSS_UNITS = ['px','%','em','rem','vh','vw','vmin','vmax','pt','pc','in','cm','mm','ex','ch','fr','deg','s','ms'];

function emSplitCssToken(tok){
  var m = tok.match(/^(-?[0-9]*\.?[0-9]+)([a-zA-Z%]*)$/);
  if (!m) return tok;
  var num = m[1], unit = m[2];
  if (unit === '') return num + (num === '0' ? '' : 'px');
  if (CSS_UNITS.indexOf(unit) !== -1) return num + unit;
  var numPart = num + (num === '0' ? '' : 'px');
  var kw = CSS_VALUE_KEYWORDS[unit] || unit;
  return numPart + ' ' + kw;
}

function expandCssFuzzy(word){
  var keys = Object.keys(CSS_PROP_PREFIXES).sort(function(a,b){return b.length-a.length;});
  for (var k=0;k<keys.length;k++){
    var pre = keys[k];
    if (word.length > pre.length && word.indexOf(pre) === 0 && /^[0-9]/.test(word.slice(pre.length))) {
      var valuePart = word.slice(pre.length);
      var tokens = valuePart.split('-').map(emSplitCssToken);
      return CSS_PROP_PREFIXES[pre] + ': ' + tokens.join(' ') + ';';
    }
  }
  return null;
}

function emApplyResult(cmi, from, to, res){
  var line = cmi.getLine(from.line);
  var indentMatch = line.match(/^\s*/);
  var baseIndent = indentMatch ? indentMatch[0] : '';
  var parts = res.text.split('\\n');
  var text = parts.map(function(l,idx){ return idx===0 ? l : baseIndent+l; }).join('\\n');
  var before2 = res.text.slice(0, res.cursorOffset);
  var nlCount = (before2.match(/\\n/g)||[]).length;
  var newOffset = res.cursorOffset + baseIndent.length*nlCount;
  cmi.replaceRange(text, from, to);
  var startIdx = cmi.indexFromPos(from);
  var pos = cmi.posFromIndex(startIdx + newOffset);
  cmi.setCursor(pos);
}

function emExtractAbbrev(line, endCh){
  var i = endCh, braceDepth = 0, bracketDepth = 0;
  var allowed = /[a-zA-Z0-9._#\[\]{}*+>^()$=:"'%,!\/-]/;
  while (i > 0) {
    var ch = line[i-1];
    var stop = false;
    if (ch === '}') braceDepth++;
    else if (ch === '{') { if (braceDepth>0) braceDepth--; else stop = true; }
    else if (ch === ']') bracketDepth++;
    else if (ch === '[') { if (bracketDepth>0) bracketDepth--; else stop = true; }
    else if (braceDepth===0 && bracketDepth===0) {
      if (ch === ' ' || !allowed.test(ch)) stop = true;
    }
    if (stop) break;
    i--;
  }
  return line.slice(i, endCh);
}

var SNIPPETS = {
  h: { 'html5': '<!DOCTYPE html>\\n<html lang="uz">\\n<head>\\n  <meta charset="UTF-8">\\n  <title>§</title>\\n</head>\\n<body>\\n  §\\n</body>\\n</html>', 'com': '<!-- § -->' },
  c: {
    'col': 'color: §;', 'bg': 'background: §;', 'bgc': 'background-color: §;',
    'bgi': 'background-image: url(§);', 'w': 'width: §;', 'h': 'height: §;',
    'mw': 'max-width: §;', 'mh': 'max-height: §;', 'm': 'margin: §;', 'mt': 'margin-top: §;',
    'mb': 'margin-bottom: §;', 'ml': 'margin-left: §;', 'mr': 'margin-right: §;',
    'p': 'padding: §;', 'pt': 'padding-top: §;', 'pb': 'padding-bottom: §;',
    'd': 'display: §;', 'db': 'display: block;', 'di': 'display: inline-block;',
    'pos': 'position: §;', 'posa': 'position: absolute;', 'posr': 'position: relative;',
    'fs': 'font-size: §;', 'fw': 'font-weight: §;', 'ff': 'font-family: §;',
    'ta': 'text-align: §;', 'tac': 'text-align: center;', 'td': 'text-decoration: §;',
    'brd': 'border: §;', 'br': 'border-radius: §;', 'bs': 'box-shadow: §;',
    'bxsd': 'box-shadow: inset 0 0 10px §;',
    'op': 'opacity: §;', 'ov': 'overflow: §;', 'z': 'z-index: §;',
    'flex': 'display: flex;', 'df': 'display: flex;', 'dg': 'display: grid;',
    'center': 'display: flex;\\n  align-items: center;\\n  justify-content: center;',
    'jcc': 'justify-content: center;', 'aic': 'align-items: center;',
    'fxd': 'flex-direction: column;', 'fxdr': 'flex-direction: row;',
    'fxdc': 'flex-direction: column;', 'fxdw': 'flex-flow: row wrap;',
    'fxww': 'flex-wrap: wrap;',
    'grid': 'display: grid;', 'trs': 'transition: §;', 'cur': 'cursor: pointer;',
    'bg+': 'background: #fff url(§) 0 0 no-repeat;'
  },
  j: {
    'fn': 'function §() {\\n  \\n}', 'af': '(§) => {\\n  \\n}', 'anfn': '(§) => {\\n  \\n}',
    'cl': 'console.log(§);', 'clg': 'console.log(§);', 'ce': 'console.error(§);',
    'fori': 'for (let i = 0; i < §.length; i++) {\\n  \\n}',
    'forof': 'for (const item of §) {\\n  \\n}',
    'fe': '§.forEach(item => {\\n  \\n});',
    'imp': "import § from '';", 'exp': 'export default §;',
    'asf': 'async function §() {\\n  \\n}', 'awt': 'await §;',
    'setT': 'setTimeout(() => {\\n  §\\n}, 1000);', 'sto': 'setTimeout(() => {\\n  §\\n}, 1000);',
    'addE': "addEventListener('§', () => {\\n  \\n});",
    'qs': "document.querySelector('§');", 'qsa': "document.querySelectorAll('§');",
    'ifj': 'if (§) {\\n  \\n}'
  }
};

function insertSnippet(cmi, from, to, snip){
  var idx = snip.indexOf('§');
  var text = idx>=0 ? (snip.slice(0,idx)+snip.slice(idx+1)) : snip;
  cmi.replaceRange(text, from, to);
  if (idx>=0){
    var pre = text.slice(0, idx);
    var lines = pre.split('\\n');
    var line = from.line + lines.length - 1;
    var ch = lines.length===1 ? (from.ch + lines[0].length) : lines[lines.length-1].length;
    cmi.setCursor({line: line, ch: ch});
  }
}

function trySnippetExpand(cmi){
  var cur = cmi.getCursor();
  var line = cmi.getLine(cur.line);
  var before = line.slice(0, cur.ch);
  if (activeTab === 'h') {
    var abbr = emExtractAbbrev(line, cur.ch);
    if (abbr) {
      var res = expandEmmetHTML(abbr);
      if (res) {
        var from = {line: cur.line, ch: cur.ch - abbr.length};
        emApplyResult(cmi, from, cur, res);
        return true;
      }
    }
    var mh = before.match(/[a-zA-Z0-9-]+$/);
    if (mh && SNIPPETS.h[mh[0]]) {
      var fh = {line: cur.line, ch: cur.ch - mh[0].length};
      insertSnippet(cmi, fh, cur, SNIPPETS.h[mh[0]]);
      return true;
    }
    return false;
  }
  if (activeTab === 'c') {
    var mc = before.match(/[a-zA-Z0-9%.+-]+$/);
    if (mc) {
      var word = mc[0];
      var fc = {line: cur.line, ch: cur.ch - word.length};
      if (SNIPPETS.c[word]) { insertSnippet(cmi, fc, cur, SNIPPETS.c[word]); return true; }
      var fz = expandCssFuzzy(word);
      if (fz) {
        cmi.replaceRange(fz, fc, cur);
        cmi.setCursor({line: fc.line, ch: fc.ch + fz.length});
        return true;
      }
    }
    return false;
  }
  var dict = SNIPPETS[activeTab];
  if (!dict) return false;
  var m = before.match(/[a-zA-Z0-9-]+$/);
  if (!m) return false;
  var word2 = m[0];
  var snip = dict[word2];
  if (!snip) return false;
  var from2 = {line: cur.line, ch: cur.ch - word2.length};
  insertSnippet(cmi, from2, cur, snip);
  return true;
}

function customHint(cmi){
  var dict = SNIPPETS[activeTab] || {};
  var cur = cmi.getCursor();
  var line = cmi.getLine(cur.line);
  var before = line.slice(0, cur.ch);
  var m = before.match(/[a-zA-Z0-9-]+$/);
  var word = m ? m[0] : '';
  if (!word) return null;
  var from = {line: cur.line, ch: cur.ch - word.length};
  var to = cur;
  var list = [];
  Object.keys(dict).forEach(function(k){
    if (k.indexOf(word) === 0){
      (function(key){
        list.push({
          text: key,
          render: function(el){
            var preview = dict[key].replace('§','').split('\\n')[0];
            el.innerHTML = '<b>'+key+'</b><span class="cm-hint-snip">'+preview+'</span>';
          },
          hint: function(cx, data){ insertSnippet(cx, data.from, data.to, dict[key]); }
        });
      })(k);
    }
  });
  if (!list.length) return null;
  return {list: list, from: from, to: to};
}

/* ══════════════════════════════════════════════════════════════════════
   KO'P FAYLLI LOYIHA: fayl daraxti, tablar, resizer, qurilma preview,
   autosave, quick-open, global qidiruv, drag&drop, split, konsol, tarix
   ══════════════════════════════════════════════════════════════════════ */
var cm, cm2;
var docsCache = {};
var fileList = [];
var openTabs = [];
var activePath = null;
var activePath2 = null;
var expandedFolders = {};
var contextTargetPath = null;
var dirty = {};
var scheduleRun, scheduleAutosave;
var splitOn = false;
var consoleOn = false;
var userSnippets = [];
var draggedPath = null;

var IMAGE_EXT = /\.(png|jpe?g|gif|ico|webp)$/i;
var SVG_EXT = /\.svg$/i;

function modeForPath(path){
  if (SVG_EXT.test(path)) return 'xml';
  if (/\.html?$/i.test(path)) return 'htmlmixed';
  if (/\.css$/i.test(path)) return 'css';
  if (/\.js$/i.test(path)) return 'javascript';
  if (/\.json$/i.test(path)) return 'application/json';
  return 'htmlmixed';
}
function kindForPath(path){
  if (/\.html?$/i.test(path)) return 'h';
  if (/\.css$/i.test(path)) return 'c';
  return 'j';
}
function lintForPath(path){
  if (/\.js$/i.test(path)) return {options:{esversion:11, asi:true, browser:true}};
  return false;
}
function fileIcon(path){
  if (/\.html?$/i.test(path)) return '🌐';
  if (/\.css$/i.test(path)) return '🎨';
  if (/\.js$/i.test(path)) return '📜';
  if (/\.json$/i.test(path)) return '🔧';
  if (IMAGE_EXT.test(path) || SVG_EXT.test(path)) return '🖼';
  return '📄';
}
function getFileRecord(path){
  for (var i=0;i<fileList.length;i++) if (fileList[i].path===path) return fileList[i];
  return null;
}
function currentContent(path){
  if (docsCache[path]) return docsCache[path].getValue();
  var rec = getFileRecord(path);
  return rec ? (rec.content||'') : null;
}

function loadAll(){
  authFetch('/editor/fs/all/UUID').then(function(r){return r.json();}).then(function(d){
    fileList = d.files;
    renderTree();
    var entry = getFileRecord('index.html') || fileList.find(function(f){return !f.is_folder;});
    if (entry) openFile(entry.path);
  });
  authFetch('/editor/snippets').then(function(r){return r.json();}).then(function(d){
    userSnippets = d.snippets || [];
    userSnippets.forEach(function(s){
      if (!SNIPPETS[s.lang]) SNIPPETS[s.lang] = {};
      SNIPPETS[s.lang][s.trigger_key] = s.body;
    });
    renderSnippetList();
  }).catch(function(){});
}

function updateBreadcrumb(path){
  var el = document.getElementById('breadcrumb');
  if (!path){ el.innerHTML = '—'; return; }
  var parts = path.split('/');
  el.innerHTML = 'UUID_NAME &nbsp;›&nbsp; ' + parts.map(function(p,i){
    return i===parts.length-1 ? '<b>'+p+'</b>' : p;
  }).join(' / ');
}

function openFile(path, pane){
  var rec = getFileRecord(path);
  if (!rec || rec.is_folder) return;
  if (!docsCache[path]) docsCache[path] = new CodeMirror.Doc(rec.content||'', modeForPath(path));
  if (openTabs.indexOf(path)===-1) openTabs.push(path);
  if (pane === 2){
    activePath2 = path;
    if (cm2) cm2.swapDoc(docsCache[path]);
  } else {
    activePath = path;
    activeTab = kindForPath(path);
    cm.swapDoc(docsCache[path]);
    cm.setOption('mode', modeForPath(path));
    var lo = lintForPath(path);
    cm.setOption('lint', lo);
    updateBreadcrumb(path);
    scheduleRun();
    drawMinimap();
  }
  renderTabs();
  renderTree();
}

function closeTab(path){
  var idx = openTabs.indexOf(path);
  if (idx===-1) return;
  openTabs.splice(idx,1);
  if (activePath===path){
    var next = openTabs[idx] || openTabs[idx-1];
    if (next) openFile(next);
    else { activePath=null; cm.swapDoc(new CodeMirror.Doc('','htmlmixed')); updateBreadcrumb(null); }
  }
  renderTabs();
}

function renderTabs(){
  var bar = document.getElementById('tabsBar');
  bar.innerHTML = '';
  openTabs.forEach(function(p){
    var el = document.createElement('div');
    el.className = 'ftab' + (p===activePath?' act':'');
    el.onclick = function(){ openFile(p); };
    var label = document.createElement('span');
    label.textContent = fileIcon(p)+' '+p.split('/').pop()+(dirty[p]?' •':'');
    var xBtn = document.createElement('span');
    xBtn.className = 'ftabx'; xBtn.textContent = '×';
    xBtn.onclick = function(ev){ ev.stopPropagation(); closeTab(p); };
    el.appendChild(label); el.appendChild(xBtn);
    if (splitOn){
      var sp = document.createElement('span');
      sp.textContent = '⊞'; sp.title = 'O\\'ng panelda ochish';
      sp.style.marginLeft='4px'; sp.style.opacity='.6';
      sp.onclick = function(ev){ ev.stopPropagation(); openFile(p, 2); };
      el.appendChild(sp);
    }
    bar.appendChild(el);
  });
}

function doSave(path, silent){
  if (!path || !docsCache[path]) return;
  var content = docsCache[path].getValue();
  if (document.getElementById('fmtOnSave') && document.getElementById('fmtOnSave').checked){
    content = beautifyText(content, kindForPath(path));
    docsCache[path].setValue(content);
  }
  authFetch('/editor/fs/write',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uuid:'UUID',path:path,content:content})
  }).then(function(r){return r.json();}).then(function(d){
    if (d.ok){
      var rec = getFileRecord(path); if(rec) rec.content=content;
      dirty[path]=false; renderTabs();
      var ind = document.getElementById('autosaveInd');
      var now = new Date(); var hh=('0'+now.getHours()).slice(-2), mm=('0'+now.getMinutes()).slice(-2), ss=('0'+now.getSeconds()).slice(-2);
      if (ind) ind.textContent = '💾 Saqlandi ' + hh+':'+mm+':'+ss;
      if (!silent) flash('✓ Saqlandi: '+path,'gr');
    } else if (!silent) flash('✗ Saqlashda xato','rd');
  }).catch(function(){ if(!silent) flash('✗ Tarmoq xatosi','rd'); });
}
function saveActive(){ doSave(activePath, false); }

function beautifyText(v, kind){
  try{
    if (kind==='h' && window.html_beautify) return html_beautify(v,{indent_size:2, wrap_line_length:0});
    if (kind==='c' && window.css_beautify) return css_beautify(v,{indent_size:2});
    if (window.js_beautify) return js_beautify(v,{indent_size:2});
  }catch(e){}
  return v;
}
function formatActive(){
  if (!activePath) return;
  var v = docsCache[activePath].getValue();
  var nv = beautifyText(v, activeTab);
  if (nv === v){ flash('⚠ Formatlash kutubxonasi yuklanmadi','yl'); return; }
  docsCache[activePath].setValue(nv);
  flash('🧹 Tartiblandi','gr'); scheduleRun();
}

function resolveRel(base, rel){
  if (/^https?:/i.test(rel)) return null;
  rel = rel.replace(/^\//,'');
  var baseDir = base.indexOf('/')>=0 ? base.slice(0,base.lastIndexOf('/')+1) : '';
  var parts = (baseDir+rel).split('/'); var out=[];
  parts.forEach(function(p){ if(p==='..') out.pop(); else if(p!=='.'&&p!=='') out.push(p); });
  return out.join('/');
}
function findEntry(){
  if (getFileRecord('index.html')) return 'index.html';
  var htmlFile = fileList.find(function(f){ return !f.is_folder && /\.html?$/i.test(f.path); });
  return htmlFile ? htmlFile.path : null;
}

var CONSOLE_BRIDGE = "<script>(function(){var _o=console.log,_e=console.error,_w=console.warn;"+
  "function fwd(type,args){try{parent.postMessage({__consoleFwd:true,ctype:type,msg:Array.prototype.slice.call(args).map(function(a){"+
  "try{return typeof a==='object'?JSON.stringify(a):String(a);}catch(e){return String(a);}}).join(' ')},'*');}catch(e){}}"+
  "console.log=function(){fwd('log',arguments);_o.apply(console,arguments);};"+
  "console.error=function(){fwd('error',arguments);_e.apply(console,arguments);};"+
  "console.warn=function(){fwd('warn',arguments);_w.apply(console,arguments);};"+
  "window.onerror=function(m){fwd('error',[m]);};})();<\/script>";

function buildPreviewHtml(){
  var entry = findEntry();
  if (!entry) return '<html><body style="font-family:sans-serif;padding:24px;color:#888">index.html topilmadi. Fayl daraxtida yarating.</body></html>';
  var html = currentContent(entry) || '';
  html = html.replace(/<link[^>]+href=["']([^"'>]+\.css)["'][^>]*>/gi, function(m, href){
    var rp = resolveRel(entry, href); if(!rp) return m;
    var c = currentContent(rp);
    return c!=null ? '<style>'+c+'</style>' : m;
  });
  html = html.replace(/<script[^>]+src=["']([^"'>]+\.js)["'][^>]*><\/script>/gi, function(m, src){
    var rp = resolveRel(entry, src); if(!rp) return m;
    var c = currentContent(rp);
    return c!=null ? '<script>'+c+'<\/script>' : m;
  });
  if (/<head[^>]*>/i.test(html)) html = html.replace(/<head([^>]*)>/i, '<head$1>'+CONSOLE_BRIDGE);
  else html = CONSOLE_BRIDGE + html;
  return html;
}
function runCode(){
  try{
    document.getElementById('pf').srcdoc = buildPreviewHtml();
    flash('✓ Yangilandi','gr');
  }catch(e){ flash('✗ Xato','rd'); }
}
window.addEventListener('message', function(ev){
  var d = ev.data;
  if (!d || !d.__consoleFwd) return;
  if (!consoleOn) return;
  var panel = document.getElementById('consolePanel');
  var line = document.createElement('div');
  line.className = 'cline c'+(d.ctype==='error'?'err':(d.ctype==='warn'?'warn':'log'));
  line.textContent = '['+d.ctype+'] '+d.msg;
  panel.appendChild(line);
  panel.scrollTop = panel.scrollHeight;
});
function toggleConsole(){
  consoleOn = !consoleOn;
  document.getElementById('consolePanel').style.display = consoleOn ? 'block':'none';
}

function buildTree(){
  var root = {name:'',path:'',is_folder:1,children:{}};
  fileList.slice().sort(function(a,b){return a.path.localeCompare(b.path);}).forEach(function(item){
    var parts = item.path.split('/');
    var node = root;
    for (var i=0;i<parts.length;i++){
      var name = parts[i]; var isLast = i===parts.length-1;
      var p = parts.slice(0,i+1).join('/');
      if (!node.children[p]) node.children[p] = {name:name, path:p, is_folder: isLast? item.is_folder:1, children:{}};
      node = node.children[p];
    }
  });
  return root;
}
function renderTree(){
  var root = buildTree();
  var host = document.getElementById('fileTree');
  host.innerHTML='';
  renderTreeNode(root, host, 0);
}
function moveFile(oldp, newp){
  if (oldp===newp) return;
  authFetch('/editor/fs/rename',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uuid:'UUID',old_path:oldp,new_path:newp})
  }).then(function(r){return r.json();}).then(function(d){ if(d.ok) loadAll(); else flash('✗ Ko\\'chirishda xato','rd'); });
}
function renderTreeNode(node, host, depth){
  var keys = Object.keys(node.children).sort(function(a,b){
    var na=node.children[a], nb=node.children[b];
    if (na.is_folder!==nb.is_folder) return nb.is_folder-na.is_folder;
    return na.name.localeCompare(nb.name);
  });
  keys.forEach(function(k){
    var n = node.children[k];
    var row = document.createElement('div');
    row.className = 'frow'+(n.path===activePath?' act':'');
    row.style.paddingLeft = (10+depth*14)+'px';
    row.draggable = true;
    row.oncontextmenu = (function(nn){ return function(e){ e.preventDefault(); e.stopPropagation(); contextTargetPath=nn; openCtxMenu(e,nn); }; })(n);
    row.ondragstart = (function(nn){ return function(e){ draggedPath = nn.path; e.dataTransfer.effectAllowed='move'; }; })(n);
    row.ondragover = (function(nn){ return function(e){ if(nn.is_folder){ e.preventDefault(); row.classList.add('dragover'); } }; })(n);
    row.ondragleave = function(){ row.classList.remove('dragover'); };
    row.ondrop = (function(nn){ return function(e){
      e.preventDefault(); row.classList.remove('dragover');
      if (!draggedPath || !nn.is_folder) return;
      var name = draggedPath.split('/').pop();
      moveFile(draggedPath, (nn.path+'/'+name).replace(/\/+/g,'/'));
      draggedPath = null;
    }; })(n);
    if (n.is_folder){
      var expanded = !!expandedFolders[n.path];
      row.innerHTML = '<span class="fic">'+(expanded?'📂':'📁')+'</span><span>'+n.name+'</span>';
      row.onclick = (function(nn,exp){ return function(){ expandedFolders[nn.path]=!exp; renderTree(); }; })(n,expanded);
      host.appendChild(row);
      if (expanded) renderTreeNode(n, host, depth+1);
    } else {
      var isImg = IMAGE_EXT.test(n.path) || SVG_EXT.test(n.path);
      row.innerHTML = '<span class="fic">'+fileIcon(n.path)+'</span><span>'+n.name+(dirty[n.path]?' •':'')+'</span>';
      row.onclick = (function(nn){ return function(){ openFile(nn.path); }; })(n);
      host.appendChild(row);
    }
  });
}

function openCtxMenu(e, node){
  contextTargetPath = node;
  var menu = document.getElementById('ctxMenu');
  menu.style.left = e.pageX+'px'; menu.style.top = e.pageY+'px';
  menu.style.display='block';
}
document.addEventListener('click', function(){ document.getElementById('ctxMenu').style.display='none'; });

function ctxBaseDir(){
  if (!contextTargetPath) return '';
  if (contextTargetPath.is_folder) return contextTargetPath.path+'/';
  var idx = contextTargetPath.path.lastIndexOf('/');
  return idx>=0 ? contextTargetPath.path.slice(0,idx+1) : '';
}
function maybeAutoImport(path){
  var idx = getFileRecord('index.html');
  if (!idx) return;
  var isCss = /\.css$/i.test(path), isJs = /\.js$/i.test(path);
  if (!isCss && !isJs) return;
  if (!confirm((isCss?'CSS':'JS')+" faylini index.html ga avtomatik ulaymi? ("+path+")")) return;
  var html = idx.content || '';
  if (isCss){
    if (html.indexOf(path) === -1 && /<\/head>/i.test(html))
      html = html.replace(/<\/head>/i, '  <link rel="stylesheet" href="'+path+'">\\n</head>');
  } else {
    if (html.indexOf(path) === -1 && /<\/body>/i.test(html))
      html = html.replace(/<\/body>/i, '  <script src="'+path+'"><\/script>\\n</body>');
  }
  idx.content = html;
  if (docsCache['index.html']) docsCache['index.html'].setValue(html);
  authFetch('/editor/fs/write',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uuid:'UUID',path:'index.html',content:html})}).then(function(){ scheduleRun(); });
}
function ctxNewFile(){
  var base = ctxBaseDir();
  var name = prompt('Yangi fayl nomi:', 'yangi.html');
  if (!name) return;
  var path = (base+name).replace(/\/+/g,'/').replace(/^\//,'');
  authFetch('/editor/fs/mkfile',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uuid:'UUID',path:path,content:''})
  }).then(function(r){return r.json();}).then(function(d){
    if (d.ok){ fileList.push({path:path,is_folder:false,content:''}); renderTree(); openFile(path); maybeAutoImport(path); }
    else alert("Xato: fayl allaqachon mavjud bo'lishi mumkin");
  });
}
function ctxNewFolder(){
  var base = ctxBaseDir();
  var name = prompt('Yangi papka nomi:', 'papka');
  if (!name) return;
  var path = (base+name).replace(/\/+/g,'/').replace(/^\//,'');
  authFetch('/editor/fs/mkdir',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uuid:'UUID',path:path})
  }).then(function(r){return r.json();}).then(function(d){
    if (d.ok){ fileList.push({path:path,is_folder:true,content:null}); expandedFolders[path]=true; renderTree(); }
    else alert("Xato: papka allaqachon mavjud bo'lishi mumkin");
  });
}
function ctxRename(){
  if (!contextTargetPath) return;
  var oldp = contextTargetPath.path;
  var name = prompt('Yangi nom:', oldp.split('/').pop());
  if (!name) return;
  var idx = oldp.lastIndexOf('/');
  var parent = idx>=0 ? oldp.slice(0,idx+1) : '';
  var newp = parent+name;
  moveFile(oldp, newp);
}
function ctxDelete(){
  if (!contextTargetPath) return;
  if (!confirm("O'chirishni tasdiqlaysizmi? "+contextTargetPath.path)) return;
  var p = contextTargetPath.path;
  authFetch('/editor/fs/delete',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uuid:'UUID',path:p})
  }).then(function(r){return r.json();}).then(function(d){
    if (d.ok){ if (openTabs.indexOf(p)>=0) closeTab(p); loadAll(); }
  });
}

function setupResizer(){
  var resizer = document.getElementById('resizer');
  var codePane = document.getElementById('codePane');
  var dragging=false;
  resizer.addEventListener('mousedown', function(e){ dragging=true; document.body.style.cursor='col-resize'; e.preventDefault(); });
  window.addEventListener('mousemove', function(e){
    if (!dragging) return;
    var wrap = document.getElementById('ebMain').getBoundingClientRect();
    var sidebarW = document.getElementById('sidebar').offsetWidth;
    var x = e.clientX - wrap.left - sidebarW;
    var totalW = wrap.width - sidebarW - 6;
    var pct = Math.min(78, Math.max(18, (x/totalW)*100));
    codePane.style.flex = '0 0 '+pct+'%';
    cm.refresh(); if(cm2) cm2.refresh();
  });
  window.addEventListener('mouseup', function(){ if(dragging){dragging=false; document.body.style.cursor='';} });
}

function setDevice(mode){
  document.getElementById('pvwrap').className = 'pvwrap '+mode;
  ['devDesktop','devTablet','devMobile'].forEach(function(id){document.getElementById(id).classList.remove('on');});
  document.getElementById('dev'+mode.charAt(0).toUpperCase()+mode.slice(1)).classList.add('on');
}
function toggleFullscreen(){
  var wrap = document.getElementById('pvwrap');
  if (!document.fullscreenElement) { if (wrap.requestFullscreen) wrap.requestFullscreen(); }
  else { if (document.exitFullscreen) document.exitFullscreen(); }
}

/* ── Split-view: ikkinchi CodeMirror panel ────────────────────────────── */
function toggleSplit(){
  splitOn = !splitOn;
  var host2 = document.getElementById('cmHost2');
  host2.style.display = splitOn ? 'block' : 'none';
  if (splitOn && !cm2){
    cm2 = CodeMirror(host2, {value:'', mode:'htmlmixed', theme:'dracula', lineNumbers:true,
      lineWrapping:true, tabSize:2, indentUnit:2, matchBrackets:true, styleActiveLine:true});
  }
  renderTabs();
  setTimeout(function(){ cm.refresh(); if(cm2) cm2.refresh(); }, 50);
}

/* ── Mini-xarita (soddalashtirilgan kod xaritasi) ─────────────────────── */
function drawMinimap(){
  var canvas = document.getElementById('minimap');
  var ctx = canvas.getContext('2d');
  var h = document.getElementById('cmHost').clientHeight || 600;
  canvas.height = h;
  ctx.clearRect(0,0,canvas.width,canvas.height);
  ctx.fillStyle = '#0a0c14'; ctx.fillRect(0,0,canvas.width,canvas.height);
  if (!activePath || !docsCache[activePath]) return;
  var doc = docsCache[activePath];
  var lines = doc.getValue().split('\\n');
  var scale = Math.min(2, h / Math.max(1,lines.length));
  ctx.fillStyle = '#7c6fff88';
  lines.forEach(function(l,i){
    var y = i*scale;
    if (y>h) return;
    var w = Math.min(canvas.width-6, (l.length||0)*0.9);
    ctx.fillRect(3, y, w, Math.max(1,scale-0.4));
  });
  canvas.onclick = function(e){
    var rect = canvas.getBoundingClientRect();
    var frac = (e.clientY-rect.top)/rect.height;
    var target = Math.floor(frac*lines.length);
    cm.setCursor({line:target, ch:0});
    cm.scrollIntoView({line:target,ch:0}, 100);
  };
}

/* ══════════════════════════════════════════════════════════════════════
   QUICK OPEN (Ctrl+P) — fayllar orasida tez qidirib ochish
   ══════════════════════════════════════════════════════════════════════ */
var qoSelIndex = 0, qoFiltered = [];

function openQuickOpen(){
  var bg = document.getElementById('quickOpenBg');
  var inp = document.getElementById('quickOpenInput');
  bg.style.display = 'flex';
  inp.value = '';
  inp.focus();
  renderQuickOpenList('');
}
function renderQuickOpenList(q){
  var list = document.getElementById('quickOpenList');
  qoFiltered = fileList.filter(function(f){
    return !f.is_folder && (!q || f.path.toLowerCase().indexOf(q.toLowerCase())!==-1);
  }).sort(function(a,b){ return a.path.length - b.path.length; });
  qoSelIndex = 0;
  list.innerHTML = '';
  qoFiltered.forEach(function(f, i){
    var row = document.createElement('div');
    row.className = 'modalRow' + (i===0 ? ' sel' : '');
    row.innerHTML = '<span>'+fileIcon(f.path)+' '+f.path+'</span><small>'+(dirty[f.path]?'●':'')+'</small>';
    row.onclick = function(){ openFile(f.path); closeModal('quickOpenBg'); };
    list.appendChild(row);
  });
  if (!qoFiltered.length) list.innerHTML = '<div class="modalRow"><small>Hech narsa topilmadi</small></div>';
}
document.addEventListener('DOMContentLoaded', function(){
  var inp = document.getElementById('quickOpenInput');
  inp.addEventListener('input', function(){ renderQuickOpenList(inp.value); });
  inp.addEventListener('keydown', function(e){
    var rows = document.querySelectorAll('#quickOpenList .modalRow');
    if (e.key === 'ArrowDown'){ e.preventDefault(); qoSelIndex = Math.min(rows.length-1, qoSelIndex+1); }
    else if (e.key === 'ArrowUp'){ e.preventDefault(); qoSelIndex = Math.max(0, qoSelIndex-1); }
    else if (e.key === 'Enter'){ if (qoFiltered[qoSelIndex]){ openFile(qoFiltered[qoSelIndex].path); closeModal('quickOpenBg'); } return; }
    else if (e.key === 'Escape'){ closeModal('quickOpenBg'); return; }
    else return;
    rows.forEach(function(r,i){ r.classList.toggle('sel', i===qoSelIndex); });
    if (rows[qoSelIndex]) rows[qoSelIndex].scrollIntoView({block:'nearest'});
  });
  document.getElementById('quickOpenBg').addEventListener('click', function(e){
    if (e.target.id === 'quickOpenBg') closeModal('quickOpenBg');
  });
});

/* ══════════════════════════════════════════════════════════════════════
   GLOBAL QIDIRUV / ALMASHTIRISH — barcha loyiha fayllari ichidan
   ══════════════════════════════════════════════════════════════════════ */
function openGlobalSearch(){
  document.getElementById('globalSearchBg').style.display = 'flex';
  document.getElementById('gsQuery').focus();
  document.getElementById('gsResults').innerHTML = '';
}
function allFileContents(){
  var map = {};
  fileList.forEach(function(f){
    if (!f.is_folder) map[f.path] = docsCache[f.path] ? docsCache[f.path].getValue() : (f.content||'');
  });
  return map;
}
function runGlobalSearch(){
  var q = document.getElementById('gsQuery').value;
  var results = document.getElementById('gsResults');
  results.innerHTML = '';
  if (!q){ results.innerHTML = '<div class="modalRow"><small>So\\'z kiriting</small></div>'; return; }
  var contents = allFileContents();
  var totalHits = 0;
  Object.keys(contents).forEach(function(path){
    var lines = contents[path].split('\\n');
    lines.forEach(function(line, li){
      if (line.toLowerCase().indexOf(q.toLowerCase()) !== -1){
        totalHits++;
        var row = document.createElement('div');
        row.className = 'modalRow';
        row.innerHTML = '<span>'+fileIcon(path)+' '+path+':'+(li+1)+' — '+
          line.trim().slice(0,70).replace(/</g,'&lt;')+'</span>';
        row.onclick = (function(p,ln){ return function(){
          openFile(p); closeModal('globalSearchBg');
          setTimeout(function(){ cm.setCursor({line:ln,ch:0}); cm.scrollIntoView({line:ln,ch:0},100); }, 60);
        }; })(path, li);
        results.appendChild(row);
      }
    });
  });
  if (!totalHits) results.innerHTML = '<div class="modalRow"><small>Hech narsa topilmadi</small></div>';
}
function runGlobalReplace(){
  var q = document.getElementById('gsQuery').value;
  var rep = document.getElementById('gsReplace').value;
  if (!q) { flash('⚠ Qidiruv so\\'zi bosh','yl'); return; }
  if (!confirm("Barcha fayllarda \\""+q+"\\" ni \\""+rep+"\\" ga almashtirasizmi? Bekor qilib bo'lmaydi.")) return;
  var changed = 0;
  fileList.forEach(function(f){
    if (f.is_folder) return;
    var cur = docsCache[f.path] ? docsCache[f.path].getValue() : (f.content||'');
    if (cur.indexOf(q) === -1) return;
    var next = cur.split(q).join(rep);
    changed++;
    if (docsCache[f.path]) docsCache[f.path].setValue(next);
    f.content = next;
    authFetch('/editor/fs/write',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({uuid:'UUID',path:f.path,content:next})});
  });
  flash('✓ '+changed+' faylda almashtirildi','gr');
  closeModal('globalSearchBg');
  scheduleRun();
}

/* ══════════════════════════════════════════════════════════════════════
   FOYDALANUVCHI SNIPPETLARI (bazada saqlanadi)
   ══════════════════════════════════════════════════════════════════════ */
function openSnippets(){
  document.getElementById('snippetsBg').style.display = 'flex';
  renderSnippetList();
}
function renderSnippetList(){
  var list = document.getElementById('snpList');
  list.innerHTML = '';
  userSnippets.forEach(function(s){
    var row = document.createElement('div');
    row.className = 'modalRow';
    row.innerHTML = '<span>['+s.lang.toUpperCase()+'] '+s.trigger_key+'</span>'+
      '<button class="btn br bsm" data-id="'+s.id+'">🗑</button>';
    row.querySelector('button').onclick = function(){ delSnippet(s.id); };
    list.appendChild(row);
  });
  if (!userSnippets.length) list.innerHTML = '<div class="modalRow"><small>Hali snippet yoq</small></div>';
}
function addSnippet(){
  var lang = document.getElementById('snpLang').value;
  var trig = document.getElementById('snpTrigger').value.trim();
  var body = document.getElementById('snpBody').value;
  if (!trig || !body){ flash('⚠ Trigger va kod kiriting','yl'); return; }
  authFetch('/editor/snippets',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({lang:lang,trigger:trig,body:body})
  }).then(function(r){return r.json();}).then(function(d){
    if (d.ok){
      userSnippets.push({id:d.id, lang:lang, trigger_key:trig, body:body});
      if (!SNIPPETS[lang]) SNIPPETS[lang]={};
      SNIPPETS[lang][trig] = body;
      document.getElementById('snpTrigger').value=''; document.getElementById('snpBody').value='';
      renderSnippetList(); flash('✓ Snippet qo\\'shildi','gr');
    } else flash('✗ Xato: trigger allaqachon mavjud','rd');
  });
}
function delSnippet(id){
  authFetch('/editor/snippets/'+id, {method:'DELETE'}).then(function(r){return r.json();}).then(function(d){
    if (d.ok){
      var s = userSnippets.find(function(x){return x.id===id;});
      if (s && SNIPPETS[s.lang]) delete SNIPPETS[s.lang][s.trigger_key];
      userSnippets = userSnippets.filter(function(x){return x.id!==id;});
      renderSnippetList();
    }
  });
}

/* ══════════════════════════════════════════════════════════════════════
   VERSIYA TARIXI (har saqlashda avtomatik saqlanadigan snapshot)
   ══════════════════════════════════════════════════════════════════════ */
function openHistory(){
  if (!activePath){ flash('⚠ Avval fayl oching','yl'); return; }
  document.getElementById('historyBg').style.display = 'flex';
  document.getElementById('histTitle').textContent = '🕘 Tarix — '+activePath;
  var list = document.getElementById('histList');
  list.innerHTML = '<div class="modalRow"><small>Yuklanmoqda...</small></div>';
  authFetch('/editor/fs/history?uuid=UUID&path='+encodeURIComponent(activePath))
    .then(function(r){return r.json();}).then(function(d){
      list.innerHTML = '';
      (d.history||[]).forEach(function(h){
        var row = document.createElement('div');
        row.className = 'histItem';
        row.innerHTML = '<span>'+h.saved_at+'</span><button class="btn bgh bsm">↩ Tiklash</button>';
        row.querySelector('button').onclick = function(){
          if (!confirm('Joriy tarkib almashtiriladi. Davom etasizmi?')) return;
          docsCache[activePath].setValue(h.content);
          doSave(activePath, false);
          closeModal('historyBg');
        };
        list.appendChild(row);
      });
      if (!(d.history||[]).length) list.innerHTML = '<div class="modalRow"><small>Tarix bosh</small></div>';
    });
}

/* ══════════════════════════════════════════════════════════════════════
   YORDAM PANELI (Emmet qisqartmalari va tugmalar haqida)
   ══════════════════════════════════════════════════════════════════════ */
function openHelpPanel(){
  document.getElementById('helpBg').style.display = 'flex';
}
document.addEventListener('DOMContentLoaded', function(){
  var hbg = document.getElementById('helpBg');
  if (hbg) hbg.addEventListener('click', function(e){
    if (e.target.id === 'helpBg') closeModal('helpBg');
  });
});

/* ══════════════════════════════════════════════════════════════════════
   CHAT — Loyiha ichidagi jonli chat
   ══════════════════════════════════════════════════════════════════════ */
var chatInterval=null;
function openChatPanel(){
  document.getElementById('chatBg').style.display='flex';
  loadChat();
  if(chatInterval) clearInterval(chatInterval);
  chatInterval=setInterval(loadChat,3000);
}
function loadChat(){
  authFetch('/api/chat/UUID/messages').then(function(r){return r.json();}).then(function(d){
    var box=document.getElementById('chatMessages');
    box.innerHTML=(d.messages||[]).map(function(m){
      return '<div style="margin-bottom:6px"><b style="color:var(--ac);font-size:.75rem">'+m.username+'</b> <span class="tm" style="font-size:.65rem">'+m.created_at.slice(11,16)+'</span><br><span>'+m.message+'</span></div>';
    }).join('') || '<p class="tm" style="text-align:center;margin-top:20px">Hali xabar yoq</p>';
    box.scrollTop=box.scrollHeight;
  });
}
function sendChat(){
  var inp=document.getElementById('chatInput');
  var msg=inp.value.trim();
  if(!msg) return;
  authFetch('/api/chat/UUID/send',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({message:msg})}).then(function(){inp.value='';loadChat();});
}
document.addEventListener('DOMContentLoaded',function(){
  document.getElementById('chatBg').addEventListener('click',function(e){if(e.target.id==='chatBg'){closeModal('chatBg');if(chatInterval)clearInterval(chatInterval);}});
});

/* ══════════════════════════════════════════════════════════════════════
   TODO — Loyiha vazifalar ro'yxati
   ══════════════════════════════════════════════════════════════════════ */
function openTodoPanel(){
  document.getElementById('todoBg').style.display='flex';
  loadTodos();
}
function loadTodos(){
  authFetch('/api/todos/UUID').then(function(r){return r.json();}).then(function(d){
    var list=document.getElementById('todoList');
    list.innerHTML=(d.todos||[]).map(function(t){
      var pri={'high':'🔴','normal':'🟡','low':'🟢'}[t.priority]||'🟡';
      return '<div class="modalRow" style="'+(t.is_done?'opacity:.5;text-decoration:line-through':'')+'"><span>'+pri+' '+t.title+'</span><span class="fl"><button class="btn bgh bsm" onclick="toggleTodo('+t.id+','+(!t.is_done)+')">✓</button><button class="btn br bsm" onclick="delTodo('+t.id+')">🗑</button></span></div>';
    }).join('') || '<div class="modalRow"><small>Vazifa yoq</small></div>';
  });
}
function addTodo(){
  var inp=document.getElementById('todoInput');var title=inp.value.trim();
  var pri=document.getElementById('todoPriority').value;
  if(!title){flash('⚠ Vazifa kiriting','yl');return;}
  authFetch('/api/todos/UUID',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({title:title,priority:pri})}).then(function(r){return r.json();}).then(function(d){if(d.ok){inp.value='';loadTodos();flash('✓ Qo\\'shildi','gr');}});
}
function toggleTodo(id,done){
  authFetch('/api/todos/UUID/'+id,{method:'PUT',headers:{'Content-Type':'application/json'},body:JSON.stringify({is_done:done})}).then(function(){loadTodos();});
}
function delTodo(id){
  authFetch('/api/todos/UUID/'+id,{method:'DELETE'}).then(function(){loadTodos();});
}
document.addEventListener('DOMContentLoaded',function(){document.getElementById('todoBg').addEventListener('click',function(e){if(e.target.id==='todoBg')closeModal('todoBg');});});

/* ══════════════════════════════════════════════════════════════════════
   KOMPONENT KUTUBXONASI
   ══════════════════════════════════════════════════════════════════════ */
function openComponentsPanel(){
  document.getElementById('compBg').style.display='flex';
  authFetch('/api/components').then(function(r){return r.json();}).then(function(d){
    var list=document.getElementById('compList');
    list.innerHTML=(d.components||[]).map(function(c){
      return '<div class="modalRow" style="flex-direction:column;align-items:flex-start"><div class="fl" style="width:100%"><b style="color:#fff;font-size:.82rem">'+c.name+'</b><span class="bx xp mla">'+c.category+'</span><button class="btn bp bsm" onclick="insertComponent('+JSON.stringify(JSON.stringify(c.code))+')">+ Qo\\'shish</button></div></div>';
    }).join('');
  });
}
function insertComponent(code){
  if(!cm||!activePath) return;
  var cur=cm.getCursor();
  cm.replaceRange(JSON.parse(code)+'\\n',cur);
  closeModal('compBg');
  flash('✓ Komponent qo\\'shildi','gr');
  scheduleRun();
}
document.addEventListener('DOMContentLoaded',function(){document.getElementById('compBg').addEventListener('click',function(e){if(e.target.id==='compBg')closeModal('compBg');});});

/* ══════════════════════════════════════════════════════════════════════
   COLOR PICKER
   ══════════════════════════════════════════════════════════════════════ */
function openColorPicker(){
  document.getElementById('colorBg').style.display='flex';
  loadPalettes();
  document.getElementById('colorPickerInput').oninput=function(){document.getElementById('colorHexVal').value=this.value;};
}
function loadPalettes(){
  authFetch('/api/color/palette').then(function(r){return r.json();}).then(function(d){
    var box=document.getElementById('colorPalettes');
    var html='';
    Object.keys(d.palettes||{}).forEach(function(name){
      html+='<p style="color:var(--mt);font-size:.72rem;margin:8px 0 4px">'+name+'</p><div style="display:flex;flex-wrap:wrap;gap:4px">';
      d.palettes[name].forEach(function(c){
        html+='<div onclick="pickColor(\\''+c+'\\')" style="width:24px;height:24px;border-radius:4px;cursor:pointer;background:'+c+';border:1px solid var(--brd)" title="'+c+'"></div>';
      });
      html+='</div>';
    });
    box.innerHTML=html;
  });
}
function pickColor(c){document.getElementById('colorHexVal').value=c;document.getElementById('colorPickerInput').value=c;}
function insertColor(){
  var c=document.getElementById('colorHexVal').value;
  if(!cm||!activePath) return;
  var cur=cm.getCursor();
  cm.replaceRange(c,cur);
  closeModal('colorBg');
  flash('✓ Rang qo\\'shildi: '+c,'gr');
}
document.addEventListener('DOMContentLoaded',function(){document.getElementById('colorBg').addEventListener('click',function(e){if(e.target.id==='colorBg')closeModal('colorBg');});});

/* ══════════════════════════════════════════════════════════════════════
   TERMINAL
   ══════════════════════════════════════════════════════════════════════ */
function openTerminal(){document.getElementById('termBg').style.display='flex';document.getElementById('termInput').focus();}
function runTermCmd(){
  var inp=document.getElementById('termInput');var cmd=inp.value.trim();
  if(!cmd) return;
  var out=document.getElementById('termOutput');
  out.innerHTML+='<span style="color:var(--ac)">$ '+cmd+'</span>\\n';
  inp.value='';
  authFetch('/api/terminal/exec',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({command:cmd})}).then(function(r){return r.json();}).then(function(d){
    if(d.ok) out.innerHTML+='<span>'+((d.output||'').replace(/</g,'&lt;'))+'</span>\\n';
    else out.innerHTML+='<span style="color:var(--rd)">Xato: '+(d.error||'')+'</span>\\n';
    out.scrollTop=out.scrollHeight;
  }).catch(function(){out.innerHTML+='<span style="color:var(--rd)">Tarmoq xatosi</span>\\n';});
}
document.addEventListener('DOMContentLoaded',function(){document.getElementById('termBg').addEventListener('click',function(e){if(e.target.id==='termBg')closeModal('termBg');});});

/* ══════════════════════════════════════════════════════════════════════
   PWA GENERATOR
   ══════════════════════════════════════════════════════════════════════ */
function generatePWA(){
  if(!confirm('Loyihaga PWA fayllarni (manifest.json, sw.js) qo\\'shish va index.html ni yangilashni xohlaysizmi?')) return;
  authFetch('/api/pwa/generate/UUID',{method:'POST'}).then(function(r){return r.json();}).then(function(d){
    if(d.ok){flash('✓ PWA yaratildi: '+d.files.join(', '),'gr');loadAll();}
    else flash('✗ Xato','rd');
  });
}

/* ══════════════════════════════════════════════════════════════════════
   README GENERATOR
   ══════════════════════════════════════════════════════════════════════ */
function generateReadme(){
  if(!confirm('README.md faylni avtomatik yaratish/yangilashni xohlaysizmi?')) return;
  authFetch('/api/readme/generate/UUID',{method:'POST'}).then(function(r){return r.json();}).then(function(d){
    if(d.ok){flash('✓ README.md yaratildi','gr');loadAll();}
    else flash('✗ Xato','rd');
  });
}

/* ══════════════════════════════════════════════════════════════════════
   RASM DRAG&DROP YUKLASH
   ══════════════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded',function(){
  var cmHost=document.getElementById('cmHost');
  if(!cmHost) return;
  cmHost.addEventListener('dragover',function(e){e.preventDefault();e.dataTransfer.dropEffect='copy';cmHost.style.outline='2px dashed var(--ac)';});
  cmHost.addEventListener('dragleave',function(){cmHost.style.outline='';});
  cmHost.addEventListener('drop',function(e){
    e.preventDefault();cmHost.style.outline='';
    var files=e.dataTransfer.files;
    if(!files.length) return;
    var file=files[0];
    if(!file.type.startsWith('image/')){flash('⚠ Faqat rasm fayllar','yl');return;}
    var fd=new FormData();fd.append('image',file);
    authFetch('/editor/upload-image/UUID',{method:'POST',body:fd}).then(function(r){return r.json();}).then(function(d){
      if(d.ok){
        var tag='<img src="'+d.url+'" alt="'+d.filename+'">';
        if(cm&&activePath) cm.replaceRange(tag+'\\n',cm.getCursor());
        flash('✓ Rasm yuklandi va qo\\'shildi','gr');
        scheduleRun();
      } else flash('✗ '+(d.error||'Xato'),'rd');
    });
  });
});

/* ══════════════════════════════════════════════════════════════════════
   BACKEND ROUTE'LAR (loyiha ichidagi mini-serverless funksiyalar)
   ══════════════════════════════════════════════════════════════════════ */
var beRoutes = [];

function openBackendPanel(){
  document.getElementById('backendBg').style.display = 'flex';
  beRefresh();
}
function beRefresh(){
  authFetch('/editor/backend/UUID').then(function(r){return r.json();}).then(function(d){
    beRoutes = d.routes || [];
    renderBackendList();
  });
}
function renderBackendList(){
  var list = document.getElementById('beList');
  list.innerHTML = '';
  beRoutes.forEach(function(r){
    var row = document.createElement('div');
    row.className = 'modalRow';
    row.innerHTML = '<span>['+r.method+'] /'+r.path+' '+(r.is_enabled?'':'<small>(o\\'chirilgan)</small>')+'</span>'+
      '<span class="fl"><button class="btn bgh bsm" data-t="tog">'+(r.is_enabled?'⏸':'▶️')+'</button>'+
      '<button class="btn br bsm" data-t="del">🗑</button></span>';
    row.querySelectorAll('button')[0].onclick = function(){ toggleBackendRoute(r.id, !r.is_enabled); };
    row.querySelectorAll('button')[1].onclick = function(){ deleteBackendRoute(r.id); };
    list.appendChild(row);
  });
  if (!beRoutes.length) list.innerHTML = '<div class="modalRow"><small>Hali backend route yoq</small></div>';
}
function addBackendRoute(){
  var method = document.getElementById('beMethod').value;
  var path = document.getElementById('bePath').value.trim();
  var code = document.getElementById('beCode').value;
  if (!path){ flash('⚠ Yo\\'l kiriting','yl'); return; }
  authFetch('/editor/backend/UUID',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({path:path,method:method,code:code})
  }).then(function(r){return r.json();}).then(function(d){
    if (d.ok){
      document.getElementById('bePath').value=''; document.getElementById('beCode').value='';
      beRefresh(); flash('✓ Route qo\\'shildi','gr');
    } else flash('✗ '+(d.error||'Xato'),'rd');
  });
}
function toggleBackendRoute(id, enabled){
  authFetch('/editor/backend/UUID/'+id,{method:'PUT',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({is_enabled:enabled})
  }).then(function(r){return r.json();}).then(function(){ beRefresh(); });
}
function deleteBackendRoute(id){
  if (!confirm('Route o\\'chirilsinmi?')) return;
  authFetch('/editor/backend/UUID/'+id,{method:'DELETE'}).then(function(r){return r.json();}).then(function(){ beRefresh(); });
}
document.addEventListener('DOMContentLoaded', function(){
  var bg = document.getElementById('backendBg');
  if (bg) bg.addEventListener('click', function(e){
    if (e.target.id === 'backendBg') closeModal('backendBg');
  });
});

/* ══════════════════════════════════════════════════════════════════════
   INITSIALIZATSIYA
   ══════════════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', function(){
  cm = new CodeMirror(document.getElementById('cmHost'), {
    value:'', mode:'htmlmixed', theme:'dracula', lineNumbers:true, lineWrapping:true, tabSize:2, indentUnit:2,
    matchBrackets:true, autoCloseBrackets:true, styleActiveLine:true, gutters:['CodeMirror-linenumbers','CodeMirror-lint-markers'],
    extraKeys: {
      'Ctrl-Space': function(cx){ CodeMirror.showHint(cx, customHint, {completeSingle:false}); },
      'Tab': function(cx){
        if (cx.state.completionActive){
          var w = cx.getRange({line:cx.getCursor().line,ch:0}, cx.getCursor());
          var m = w.match(/[a-zA-Z0-9._#\[\]{}*+>^()$=:"'%,!\/-]+$/);
          if (m && looksLikeEmmet(m[0])){ cx.closeHint(); if (trySnippetExpand(cx)) return; }
          return CodeMirror.Pass;
        }
        if (trySnippetExpand(cx)) return;
        if (cx.somethingSelected()){ cx.execCommand('indentMore'); return; }
        cx.replaceSelection('  ');
      },
      'Enter': function(cx){
        if (cx.state.completionActive) return CodeMirror.Pass;
        if ((activeTab==='h'||activeTab==='c') && trySnippetExpand(cx)) return;
        return CodeMirror.Pass;
      },
      'Ctrl-S': function(){ saveActive(); return false; },
      'Cmd-S': function(){ saveActive(); return false; },
      'Ctrl-P': function(){ openQuickOpen(); return false; },
      'Cmd-P': function(){ openQuickOpen(); return false; },
      'Ctrl-Shift-F': function(){ openGlobalSearch(); return false; },
      'Ctrl-Enter': function(){ runCode(); },
      'Cmd-Enter': function(){ runCode(); },
      'Shift-Alt-F': function(){ formatActive(); },
      'Ctrl-/': 'toggleComment',
      'Cmd-/': 'toggleComment'
    }
  });
  scheduleRun = debounce(runCode, 600);
  scheduleAutosave = debounce(function(){ if (activePath) doSave(activePath, true); }, 1500);
  cm.on('change', function(){
    if (activePath){ dirty[activePath]=true; renderTabs(); }
    scheduleRun();
    scheduleAutosave();
    drawMinimap();
  });
  cm.on('inputRead', function(cx, change){
    if (change.text.length===1 && /[a-zA-Z]/.test(change.text[0])){
      var cur = cx.getCursor();
      var before = cx.getLine(cur.line).slice(0, cur.ch);
      var m = before.match(/[a-zA-Z0-9._#\[\]{}*+>^()$=:"'%,!\/-]+$/);
      // Emmet naqshiga o'xshasa hintni ochmaymiz — Tab birinchi bosishdayoq kengaysin
      if (m && looksLikeEmmet(m[0])) return;
      CodeMirror.showHint(cx, customHint, {completeSingle:false});
    }
  });
  document.getElementById('globalSearchBg').addEventListener('click', function(e){
    if (e.target.id === 'globalSearchBg') closeModal('globalSearchBg');
  });
  document.getElementById('snippetsBg').addEventListener('click', function(e){
    if (e.target.id === 'snippetsBg') closeModal('snippetsBg');
  });
  document.getElementById('historyBg').addEventListener('click', function(e){
    if (e.target.id === 'historyBg') closeModal('historyBg');
  });
  document.addEventListener('keydown', function(e){
    if ((e.ctrlKey||e.metaKey) && e.key.toLowerCase()==='p'){ e.preventDefault(); openQuickOpen(); }
    if ((e.ctrlKey||e.metaKey) && e.shiftKey && e.key.toLowerCase()==='f'){ e.preventDefault(); openGlobalSearch(); }
  });
  setupResizer();
  loadAll();
  window.addEventListener('resize', drawMinimap);
});
</script></body></html>"""

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║              LOYIHALAR RO'YXATI, ZIP, SHARE, VERSIYA TARIXI              ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/projects")
@user_req
def projects_list():
    uid=session["user_id"]; adm=session.get("admin") or session.get("_guest")
    if adm:
        ps=db_exec("SELECT p.*,u.username FROM projects p LEFT JOIN users u ON p.owner_id=u.id ORDER BY p.updated_at DESC") or []
    else:
        ps=db_exec("SELECT p.*,u.username FROM projects p LEFT JOIN users u ON p.owner_id=u.id WHERE p.owner_id=? ORDER BY p.updated_at DESC",(uid,)) or []
    cards=""
    for p in ps:
        pub='<span class="bx xg">Ommaviy</span>' if p["is_public"] else '<span class="bx xm">Shaxsiy</span>'
        cards+=f"""
        <div class="card">
          <div class="fl mb"><b style="color:#fff">{p['name']}</b>{pub}
            <span class="bx xp mla">v{p['current_version']}</span></div>
          <p class="tm" style="font-size:.78rem;margin-bottom:12px">
            {p.get('username') or '—'} · {str(p.get('updated_at',''))[:16]}</p>
          <div class="fl">
            <a href="/editor/{p['uuid']}" class="btn bp bsm">✏️ Tahrirlash</a>
            <a href="/preview/{p['uuid']}" class="btn bgh bsm" target="_blank">👁 Ko'rish</a>
            <a href="/projects/share/{p['uuid']}" class="btn bg bsm">🔗 Share</a>
            <a href="/projects/{p['uuid']}/team" class="btn bgh bsm">🧑‍🤝‍🧑 Jamoa</a>
            <a href="/projects/download/{p['uuid']}" class="btn bgh bsm">⬇ ZIP</a>
            <button class="btn bgh bsm" onclick="showLoc('{p['uuid']}')">📍 Manzil</button>
            <form method="POST" action="/projects/delete/{p['uuid']}" onsubmit="return confirm('O\\'chirish?')" style="margin-left:auto">{csrf_field()}
              <button class="btn br bsm">🗑</button></form>
          </div>
        </div>"""
    body=f"""
    <div class="fl mb"><h2 style="color:#fff">Loyihalar</h2>
      <a href="/editor/new" class="btn bp mla">+ Yangi loyiha</a></div>
    <div class="g g3">{cards or '<div class="card"><p class="tm">Hali loyiha yo\'q. <a href="/editor/new">Yarating!</a></p></div>'}</div>
    <script>
    function showLoc(uuid){{
      fetch('/projects/location/'+uuid).then(r=>r.json()).then(d=>{{
        alert('Baza fayli manzili:\\n'+d.db_path+'\\n\\n'+d.note);
      }});
    }}
    </script>"""
    return _pg("Loyihalar",body,"projects")

@app.route("/projects/delete/<puuid>",methods=["POST"])
@user_req
@write_req
def proj_delete(puuid):
    row=q1("SELECT id FROM projects WHERE uuid=?",(puuid,))
    if row:
        db_exec("DELETE FROM project_versions WHERE project_id=?",(row["id"],),fetch=False)
        db_exec("DELETE FROM project_files WHERE project_id=?",(row["id"],),fetch=False)
        db_exec("DELETE FROM project_file_history WHERE project_id=?",(row["id"],),fetch=False)
        db_exec("DELETE FROM projects WHERE uuid=?",(puuid,),fetch=False)
    return redirect("/projects")

@app.route("/projects/share/<puuid>")
@user_req
@write_req
def proj_share(puuid):
    import html as hm
    proj=q1("SELECT * FROM projects WHERE uuid=?",(puuid,))
    if not proj: abort(404)
    tok=proj.get("share_token") or gtok(24)
    db_exec("UPDATE projects SET is_public=1,share_token=? WHERE uuid=?",(tok,puuid),fetch=False)
    port=CFG["PORT"]; ip=local_ip(); ng=_active_mode.get("url","")
    urls=[("🔒 Shaxsiy",f"http://127.0.0.1:{port}/preview/{puuid}"),
          ("📡 LAN",f"http://{ip}:{port}/preview/{puuid}"),
          ("🌍 Global",f"{ng}/preview/{puuid}" if ng else "(ngrok ishga tushirilmagan)")]
    cards="".join(f"""
    <div class="card"><div class="fl mb"><b style="color:#fff">{l}</b></div>
      <div class="urlbox">{u}</div>
      <button class="cpb mt" onclick="copyText('{u}')">Nusxalash</button>
    </div>""" for l,u in urls if "ishga" not in u) + "".join(f"""
    <div class="card"><div class="fl mb"><b style="color:#fff">{l}</b></div>
      <div class="urlbox" style="color:var(--mt)">{u}</div>
    </div>""" for l,u in urls if "ishga" in u)
    body=f"""
    <div class="fl mb"><h2 style="color:#fff">Share — {hm.escape(proj['name'])}</h2>
      <a href="/projects" class="btn bgh mla">← Loyihalar</a></div>
    {cards}"""
    return _pg("Share",body,"projects")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║              VIRTUAL FS API — muharrir uchun (fetch orqali)              ║
# ╚══════════════════════════════════════════════════════════════════════════╝
HISTORY_KEEP = 20  # har fayl uchun saqlanadigan maksimal snapshot soni

def _snapshot_history(project_id, path, content):
    db_exec("INSERT INTO project_file_history (project_id,path,content) VALUES (?,?,?)",
            (project_id, path, content), fetch=False)
    old = db_exec("SELECT id FROM project_file_history WHERE project_id=? AND path=? "
                  "ORDER BY id DESC LIMIT -1 OFFSET ?", (project_id, path, HISTORY_KEEP)) or []
    for r in old:
        db_exec("DELETE FROM project_file_history WHERE id=?", (r["id"],), fetch=False)

@app.route("/editor/fs/all/<puuid>")
@user_req
def fs_all(puuid):
    proj = _proj_or_404(puuid, session["user_id"], session.get("admin") or session.get("_guest"))
    _ensure_files(proj["id"])
    rows = db_exec("SELECT path,is_folder,content FROM project_files WHERE project_id=? ORDER BY path",(proj["id"],)) or []
    return jsonify({"files":[{"path":r["path"],"is_folder":bool(r["is_folder"]),"content":r.get("content") or ""} for r in rows]})

@app.route("/editor/fs/write", methods=["POST"])
@user_req
@write_req
def fs_write():
    d = request.get_json() or {}
    proj = _proj_or_404(d.get("uuid",""), session["user_id"], session.get("admin"))
    path = (d.get("path") or "").strip().strip("/")
    if not path: return jsonify({"ok":False,"error":"Yo'l bo'sh"})
    content = d.get("content","")
    prev = q1("SELECT content FROM project_files WHERE project_id=? AND path=?", (proj["id"], path))
    if prev is not None and prev.get("content") is not None and prev["content"] != content:
        _snapshot_history(proj["id"], path, prev["content"])
    db_exec("INSERT INTO project_files (project_id,path,is_folder,content,updated_at) VALUES (?,?,0,?,datetime('now')) "
            "ON CONFLICT(project_id,path) DO UPDATE SET content=excluded.content, updated_at=datetime('now')",
            (proj["id"],path,content), fetch=False)
    db_exec("UPDATE projects SET updated_at=datetime('now') WHERE id=?", (proj["id"],), fetch=False)
    return jsonify({"ok":True})

@app.route("/editor/fs/history")
@user_req
def fs_history():
    puuid = request.args.get("uuid",""); path = request.args.get("path","")
    proj = _proj_or_404(puuid, session["user_id"], session.get("admin") or session.get("_guest"))
    rows = db_exec("SELECT id,content,saved_at FROM project_file_history WHERE project_id=? AND path=? ORDER BY id DESC LIMIT ?",
                   (proj["id"], path, HISTORY_KEEP)) or []
    return jsonify({"history":[{"id":r["id"],"content":r["content"],"saved_at":str(r["saved_at"])[:19]} for r in rows]})

@app.route("/editor/fs/mkdir", methods=["POST"])
@user_req
@write_req
def fs_mkdir():
    d = request.get_json() or {}
    proj = _proj_or_404(d.get("uuid",""), session["user_id"], session.get("admin"))
    path = (d.get("path") or "").strip().strip("/")
    if not path: return jsonify({"ok":False,"error":"Nom bo'sh"})
    ok = db_exec("INSERT OR IGNORE INTO project_files (project_id,path,is_folder,content) VALUES (?,?,1,NULL)",
                 (proj["id"],path), fetch=False)
    return jsonify({"ok":bool(ok)})

@app.route("/editor/fs/mkfile", methods=["POST"])
@user_req
@write_req
def fs_mkfile():
    d = request.get_json() or {}
    proj = _proj_or_404(d.get("uuid",""), session["user_id"], session.get("admin"))
    path = (d.get("path") or "").strip().strip("/")
    if not path: return jsonify({"ok":False,"error":"Nom bo'sh"})
    ok = db_exec("INSERT OR IGNORE INTO project_files (project_id,path,is_folder,content) VALUES (?,?,0,?)",
                 (proj["id"],path,d.get("content","")), fetch=False)
    return jsonify({"ok":bool(ok)})

@app.route("/editor/fs/rename", methods=["POST"])
@user_req
@write_req
def fs_rename():
    d = request.get_json() or {}
    proj = _proj_or_404(d.get("uuid",""), session["user_id"], session.get("admin"))
    old = (d.get("old_path") or "").strip().strip("/")
    new = (d.get("new_path") or "").strip().strip("/")
    if not old or not new: return jsonify({"ok":False})
    clash = q1("SELECT id FROM project_files WHERE project_id=? AND path=?", (proj["id"], new))
    if clash: return jsonify({"ok":False,"error":"Maqsad allaqachon mavjud"})
    rows = db_exec("SELECT * FROM project_files WHERE project_id=? AND (path=? OR path LIKE ?)",
                   (proj["id"], old, old+"/%")) or []
    for r in rows:
        np = new + r["path"][len(old):]
        db_exec("UPDATE project_files SET path=? WHERE id=?", (np, r["id"]), fetch=False)
    db_exec("UPDATE project_file_history SET path=? WHERE project_id=? AND path=?", (new, proj["id"], old), fetch=False)
    return jsonify({"ok":True})

@app.route("/editor/fs/delete", methods=["POST"])
@user_req
@write_req
def fs_delete():
    d = request.get_json() or {}
    proj = _proj_or_404(d.get("uuid",""), session["user_id"], session.get("admin"))
    path = (d.get("path") or "").strip().strip("/")
    if not path: return jsonify({"ok":False})
    db_exec("DELETE FROM project_files WHERE project_id=? AND (path=? OR path LIKE ?)",
            (proj["id"], path, path+"/%"), fetch=False)
    db_exec("DELETE FROM project_file_history WHERE project_id=? AND path=?", (proj["id"], path), fetch=False)
    return jsonify({"ok":True})

# ── Foydalanuvchi snippetlari (Emmet/kod bo'laklari, bazada saqlanadi) ────
@app.route("/editor/snippets", methods=["GET","POST"])
@user_req
def editor_snippets():
    if request.method == "GET":
        rows = db_exec("SELECT id,lang,trigger_key,body FROM user_snippets WHERE user_id=? ORDER BY trigger_key",
                       (session["user_id"],)) or []
        return jsonify({"snippets": rows})
    if role_rank(session.get("role")) < ROLE_RANK["user"]:
        return jsonify({"ok": False, "error": "Ruxsat yo'q"}), 403
    d = request.get_json() or {}
    lang = d.get("lang","j"); trig = (d.get("trigger") or "").strip(); body = d.get("body","")
    if lang not in ("h","c","j") or not trig or not body:
        return jsonify({"ok": False})
    exists = q1("SELECT id FROM user_snippets WHERE user_id=? AND lang=? AND trigger_key=?",
                (session["user_id"], lang, trig))
    if exists: return jsonify({"ok": False, "error": "Trigger allaqachon mavjud"})
    new_id = db_exec("INSERT INTO user_snippets (user_id,lang,trigger_key,body) VALUES (?,?,?,?)",
                     (session["user_id"], lang, trig, body), fetch=False)
    return jsonify({"ok": True, "id": new_id})

@app.route("/editor/snippets/<int:sid>", methods=["DELETE"])
@user_req
@write_req
def editor_snippet_delete(sid):
    db_exec("DELETE FROM user_snippets WHERE id=? AND user_id=?", (sid, session["user_id"]), fetch=False)
    return jsonify({"ok": True})

@app.route("/projects/download/<puuid>")
@user_req
def project_download(puuid):
    proj = _proj_or_404(puuid, session["user_id"], session.get("admin") or session.get("_guest"))
    _ensure_files(proj["id"])
    rows = db_exec("SELECT path,is_folder,content FROM project_files WHERE project_id=?", (proj["id"],)) or []
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        for r in rows:
            if r["is_folder"]:
                zf.writestr(r["path"].rstrip("/") + "/", "")
            else:
                zf.writestr(r["path"], r.get("content") or "")
    buf.seek(0)
    safe_name = re.sub(r'[^a-zA-Z0-9_-]+', '_', proj["name"]) or "loyiha"
    return send_file(buf, as_attachment=True, download_name=f"{safe_name}.zip", mimetype="application/zip")

@app.route("/projects/location/<puuid>")
@user_req
def project_location(puuid):
    proj = _proj_or_404(puuid, session["user_id"], session.get("admin") or session.get("_guest"))
    db_path = str(Path(CFG["DB_FILE"]).resolve())
    return jsonify({
        "db_path": db_path,
        "project_id": proj["id"],
        "note": "Loyiha fayllari alohida jismoniy papkada emas, shu SQLite baza faylida (project_files jadvalida) saqlanadi."
    })

@app.route("/editor/new",methods=["GET","POST"])
@app.route("/editor/<puuid>")
@user_req
def editor(puuid=None):
    import html as hm
    if puuid is None:
        if request.method=="POST":
            if role_rank(session.get("role")) < ROLE_RANK["user"]: abort(403)
            name=request.form.get("name","Yangi loyiha")
            uid_s=str(uuid.uuid4())
            new_id=db_exec("INSERT INTO projects (uuid,name,owner_id) VALUES (?,?,?)",
                           (uid_s,name,session["user_id"]),fetch=False)
            db_exec("INSERT INTO project_versions (project_id,version,html_code,css_code,js_code) VALUES (?,1,?,?,?)",
                    (new_id,'<!DOCTYPE html>\n<html>\n<head>\n  <meta charset="UTF-8">\n  <title>Sahifa</title>\n</head>\n<body>\n  <h1>Salom Dunyo!</h1>\n</body>\n</html>',
                     '/* CSS kodingiz */', '// JS kodingiz'),fetch=False)
            return redirect(f"/editor/{uid_s}")
        form=f'<div class="card" style="max-width:380px"><h3>Yangi loyiha</h3><form method="POST">{csrf_field()}<div class="fld"><label>Nomi</label><input name="name" required placeholder="Mening loyiham" autofocus></div><button class="btn bp">Yaratish</button><a href="/projects" class="btn bgh" style="margin-left:8px">Bekor</a></form></div>'
        return _pg("Yangi loyiha",form,"editor")
    proj=q1("SELECT * FROM projects WHERE uuid=?",(puuid,))
    if not proj: abort(404)
    is_owner = proj["owner_id"]==session["user_id"]
    if not is_owner and not session.get("admin") and not session.get("_guest"): abort(403)
    _ensure_files(proj["id"])
    page=(EDITOR_TMPL
          .replace("INSERTCSS",CSS)
          .replace("NAME",hm.escape(proj["name"]))
          .replace("CSRFTOKEN",get_csrf_token())
          .replace("UUID_NAME",hm.escape(proj["name"]))
          .replace("UUID",puuid))
    return page

@app.route("/editor/save",methods=["POST"])
@user_req
@write_req
def editor_save():
    d=request.get_json() or {}
    puuid=d.get("uuid","")
    proj=q1("SELECT * FROM projects WHERE uuid=? AND owner_id=?",(puuid,session["user_id"]))
    if not proj: return jsonify({"ok":False})
    nv=proj["current_version"]+1
    db_exec("INSERT INTO project_versions (project_id,version,html_code,css_code,js_code,notes) VALUES (?,?,?,?,?,?)",
            (proj["id"],nv,d.get("html",""),d.get("css",""),d.get("js",""),d.get("notes","")),fetch=False)
    now=datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    db_exec("UPDATE projects SET current_version=?,updated_at=? WHERE id=?",(nv,now,proj["id"]),fetch=False)
    return jsonify({"ok":True,"version":nv})

@app.route("/editor/ver/<int:vid>")
@user_req
def editor_ver(vid):
    row=q1("SELECT pv.* FROM project_versions pv JOIN projects p ON pv.project_id=p.id WHERE pv.id=?",(vid,))
    if not row: abort(404)
    return jsonify({"html":row["html_code"] or "","css":row["css_code"] or "","js":row["js_code"] or ""})

@app.route("/preview/<puuid>")
def preview(puuid):
    import html as hm
    proj=q1("SELECT * FROM projects WHERE uuid=?",(puuid,))
    if not proj: abort(404)
    is_owner=session.get("user_id")==proj["owner_id"]
    is_adm=session.get("admin",False)
    if not proj["is_public"] and not is_owner and not is_adm:
        tok=request.args.get("token","")
        if tok:
            lk=q1("SELECT * FROM links WHERE token=? AND project_id=? AND is_active=1",(tok,proj["id"]))
            if not lk: abort(403)
        elif not session.get("user_id"): return redirect("/login")
        else: abort(403)
    ver=q1("SELECT * FROM project_versions WHERE project_id=? AND version=?",(proj["id"],proj["current_version"]))
    # Ko'p fayl/papkali loyihalarda (project_files) haqiqiy sahifa index.html dan yig'iladi
    _ensure_files(proj["id"])
    pf_rows = db_exec("SELECT path,content FROM project_files WHERE project_id=? AND is_folder=0", (proj["id"],)) or []
    files_map = {r["path"]: (r.get("content") or "") for r in pf_rows}
    entry = "index.html" if "index.html" in files_map else next(iter(files_map), None)
    built = _build_page_html(files_map, entry) if entry else None
    if built is not None:
        h = built
    elif ver:
        h=ver.get("html_code","") or ""; c=ver.get("css_code","") or ""; j=ver.get("js_code","") or ""
        if c and "<style>" not in h: h=f"<style>{c}</style>\n"+h
        if j and "<script>" not in h: h+=f"\n<script>{j}</script>"
    else:
        abort(404)
    log_access("private",path=f"/preview/{puuid}")
    return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
    <title>Preview — {hm.escape(proj['name'])}</title><style>{CSS} body{{margin:0}}</style></head><body>
    <div style="background:var(--surf);color:var(--ac);padding:7px 14px;
      font-size:.75rem;border-bottom:1px solid var(--brd);display:flex;align-items:center;gap:10px">
      <span>⬡ SrvManager</span><span>·</span>
      <b style="color:#fff">{hm.escape(proj['name'])}</b>
      <span class="bx xp">v{proj['current_version']}</span>
      <a href="/editor/{puuid}" style="margin-left:auto;font-size:.73rem">✏️ Tahrirlash</a>
    </div>
    <iframe srcdoc="{hm.escape(h)}"
      sandbox="allow-scripts allow-forms allow-popups allow-same-origin"
      style="width:100%;height:calc(100vh - 36px);border:none;display:block"></iframe>
    </body></html>"""

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     GLOBAL QIDIRUV                                        ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/search")
@user_req
def search():
    q = request.args.get("q","").strip()
    uid = session["user_id"]; adm = session.get("admin") or session.get("_guest")
    links = files = projs = users = []
    if q:
        like = f"%{q}%"
        if adm:
            links = db_exec("SELECT * FROM links WHERE label LIKE ? OR token LIKE ? ORDER BY created_at DESC LIMIT 25",(like,like)) or []
            files = db_exec("SELECT * FROM files WHERE original_name LIKE ? ORDER BY created_at DESC LIMIT 25",(like,)) or []
            projs = db_exec("SELECT * FROM projects WHERE name LIKE ? ORDER BY updated_at DESC LIMIT 25",(like,)) or []
            users = db_exec("SELECT * FROM users WHERE username LIKE ? OR email LIKE ? LIMIT 25",(like,like)) or []
        else:
            links = db_exec("SELECT * FROM links WHERE owner_id=? AND (label LIKE ? OR token LIKE ?) ORDER BY created_at DESC LIMIT 25",(uid,like,like)) or []
            files = db_exec("SELECT * FROM files WHERE owner_id=? AND original_name LIKE ? ORDER BY created_at DESC LIMIT 25",(uid,like)) or []
            projs = db_exec("SELECT * FROM projects WHERE owner_id=? AND name LIKE ? ORDER BY updated_at DESC LIMIT 25",(uid,like)) or []

    def sec(title, icon, rows_html, empty_msg):
        return f"""<div class="card"><h3>{icon} {title} ({0 if not rows_html else rows_html.count('<tr')})</h3>
        <div class="tw"><table><tbody>{rows_html or f'<tr><td style="padding:14px;color:var(--mt)">{empty_msg}</td></tr>'}</tbody></table></div></div>"""

    lr = "".join(f"""<tr><td><span class="bx xp">{l['mode']}</span></td>
        <td>{l.get('label') or '—'}</td><td><code style="font-size:.72rem">{l['token'][:16]}...</code></td>
        <td><a href="/links/edit/{l['id']}" class="btn bgh bsm">Ochish</a></td></tr>""" for l in links)
    fr = "".join(f"""<tr><td>{f['original_name']}</td><td>{hsize(f.get('file_size_bytes',0))}</td>
        <td><a href="/download/{f['uuid']}" class="btn bg bsm">⬇</a></td></tr>""" for f in files)
    pr = "".join(f"""<tr><td>{p['name']}</td><td>v{p['current_version']}</td>
        <td><a href="/editor/{p['uuid']}" class="btn bp bsm">Tahrirlash</a></td></tr>""" for p in projs)
    ur = "".join(f"""<tr><td>{u['username']}</td><td>{u.get('email','')}</td>
        <td><span class="bx {'xg' if u['role']=='admin' else 'xb'}">{u['role']}</span></td></tr>""" for u in users)

    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">🔍 Qidiruv natijalari: "{q}"</h2>
    <div class="g g2">
      {sec("Havolalar","🔗",lr,"Havola topilmadi")}
      {sec("Fayllar","📁",fr,"Fayl topilmadi")}
      {sec("Loyihalar","💻",pr,"Loyiha topilmadi")}
      {sec("Foydalanuvchilar","👥",ur,"Faqat admin uchun / topilmadi") if adm else ""}
    </div>""" if q else '<div class="card"><p class="tm">Qidirish uchun so\'z kiriting.</p></div>'
    return _pg("Qidiruv", body, "search")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     STATISTIKA                                            ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/stats")
@user_req
def stats():
    def cnt(q,a=None): return (q1(q,a) or {}).get("c",0)
    tv=cnt("SELECT COUNT(*) c FROM access_logs")
    td=cnt("SELECT COUNT(*) c FROM access_logs WHERE date(visited_at)=date('now')")
    tw=cnt("SELECT COUNT(*) c FROM access_logs WHERE visited_at>datetime('now','-7 days')")
    bm=db_exec("SELECT mode,COUNT(*) cnt FROM access_logs GROUP BY mode ORDER BY cnt DESC") or []
    dy=db_exec("SELECT date(visited_at) d,COUNT(*) cnt FROM access_logs WHERE visited_at>datetime('now','-14 days') GROUP BY date(visited_at) ORDER BY d") or []
    tp=db_exec("SELECT ip_address,COUNT(*) cnt FROM access_logs GROUP BY ip_address ORDER BY cnt DESC LIMIT 10") or []
    tpath=db_exec("SELECT path,COUNT(*) cnt FROM access_logs GROUP BY path ORDER BY cnt DESC LIMIT 10") or []
    bw=db_exec("SELECT log_date,SUM(bytes_used)/1048576.0 mb FROM bandwidth_log GROUP BY log_date ORDER BY log_date DESC LIMIT 14") or []
    mr="".join(f"""<tr><td><span class="bx xp">{r['mode']}</span></td><td><b>{r['cnt']}</b></td>
      <td><div style="background:var(--brd);border-radius:4px;height:7px;overflow:hidden">
        <div style="background:var(--ac);height:100%;width:{min(100,int(r['cnt']/(tv or 1)*100))}%"></div>
      </div></td></tr>""" for r in bm)
    ir="".join(f"<tr><td><code>{r['ip_address']}</code></td><td>{r['cnt']}</td></tr>" for r in tp)
    pr="".join(f"<tr><td style='max-width:240px;overflow:hidden;text-overflow:ellipsis'><code style='font-size:.71rem'>{r['path']}</code></td><td>{r['cnt']}</td></tr>" for r in tpath)
    dl=json.dumps([str(d["d"]) for d in dy])
    dd=json.dumps([int(d["cnt"]) for d in dy])
    bl=json.dumps([str(b["log_date"]) for b in bw])
    bd=json.dumps([round(float(b["mb"] or 0),2) for b in bw])
    body=f"""
    <h2 style="color:#fff;margin-bottom:14px">📈 Statistika</h2>
    <div class="g g4 mb">
      <div class="stat"><div class="v">{tv}</div><div class="l">Jami tashriflar</div></div>
      <div class="stat"><div class="v">{td}</div><div class="l">Bugungi</div></div>
      <div class="stat"><div class="v">{tw}</div><div class="l">7 kunlik</div></div>
      <div class="stat"><div class="v">{len(bm)}</div><div class="l">Rejimlar</div></div>
    </div>
    <div class="g g2">
      <div class="card"><h3>Kunlik tashriflar (14 kun)</h3><canvas id="cd" height="200"></canvas></div>
      <div class="card"><h3>Bandwidth MB (14 kun)</h3><canvas id="cb" height="200"></canvas></div>
    </div>
    <div class="g g3 mt">
      <div class="card"><h3>Rejimlar bo'yicha</h3>
        <div class="tw"><table><thead><tr><th>Rejim</th><th>Soni</th><th>Ulush</th></tr></thead>
        <tbody>{mr}</tbody></table></div></div>
      <div class="card"><h3>Top IP manzillar</h3>
        <div class="tw"><table><thead><tr><th>IP</th><th>Soni</th></tr></thead>
        <tbody>{ir}</tbody></table></div></div>
      <div class="card"><h3>Top sahifalar</h3>
        <div class="tw"><table><thead><tr><th>Yo'l</th><th>Soni</th></tr></thead>
        <tbody>{pr}</tbody></table></div></div>
    </div>
    <script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
    <script>
    const cd={{borderColor:'#7c6fff',backgroundColor:'rgba(124,111,255,.15)',fill:true,tension:.35,pointRadius:3}};
    new Chart(document.getElementById('cd'),{{type:'line',
      data:{{labels:{dl},datasets:[{{...cd,label:'Tashriflar',data:{dd}}}]}},
      options:{{plugins:{{legend:{{display:false}}}},scales:{{
        x:{{ticks:{{color:'#5c6890'}},grid:{{color:'#252d45'}}}},
        y:{{ticks:{{color:'#5c6890'}},grid:{{color:'#252d45'}},beginAtZero:true}}}}}}
    }});
    new Chart(document.getElementById('cb'),{{type:'bar',
      data:{{labels:{bl},datasets:[{{...cd,label:'MB',type:'bar',backgroundColor:'rgba(34,211,160,.2)',borderColor:'#22d3a0',data:{bd}}}]}},
      options:{{plugins:{{legend:{{display:false}}}},scales:{{
        x:{{ticks:{{color:'#5c6890'}},grid:{{color:'#252d45'}}}},
        y:{{ticks:{{color:'#5c6890'}},grid:{{color:'#252d45'}},beginAtZero:true}}}}}}
    }});
    </script>"""
    return _pg("Statistika",body,"stats")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     ADMIN                                                 ║
# ╚══════════════════════════════════════════════════════════════════════════╗
@app.route("/admin/users")
@admin_req
def admin_users():
    us=db_exec("SELECT * FROM users ORDER BY created_at DESC") or []
    role_opts = ["viewer","user","editor","admin"]
    rows="".join(f"""<tr>
      <td>{u['id']}</td><td>{u['username']}</td><td>{u.get('email','')}</td>
      <td>
        <form method="POST" action="/admin/users/role/{u['id']}" style="display:inline-flex;gap:4px">{csrf_field()}
          <select name="role" onchange="this.form.submit()" style="padding:3px 6px;background:var(--bg);border:1px solid var(--brd);color:var(--tx);border-radius:5px;font-size:.72rem">
            {''.join(f'<option value="{r}" {"selected" if u["role"]==r else ""}>{r}</option>' for r in role_opts)}
          </select>
        </form>
      </td>
      <td>{'✓' if u['is_active'] else '✗'}</td>
      <td class="tm" style="font-size:.76rem">{str(u.get('last_login','—'))[:16]}</td>
      <td class="fl">
        <form method="POST" action="/admin/users/toggle/{u['id']}">{csrf_field()}
          <button class="btn bgh bsm">{'🔴' if u['is_active'] else '🟢'}</button></form>
        <form method="POST" action="/admin/users/del/{u['id']}" onsubmit="return confirm('O\\'chirish?')">{csrf_field()}
          <button class="btn br bsm">🗑</button></form>
      </td>
    </tr>""" for u in us)
    body=f"""<h2 style="color:#fff;margin-bottom:14px">👥 Foydalanuvchilar</h2>
    <p class="tm mb" style="font-size:.79rem">Rollar: <b>viewer</b> — faqat ko'rish, <b>user/editor</b> — yaratish/tahrirlash,
      <b>admin</b> — to'liq boshqaruv.</p>
    <div class="card" style="padding:0"><div class="tw">
      <table><thead><tr><th>#</th><th>Login</th><th>Email</th><th>Rol</th><th>Faol</th><th>Oxirgi kirish</th><th>Amallar</th></tr></thead>
      <tbody>{rows}</tbody></table></div></div>"""
    return _pg("Foydalanuvchilar",body,"users")

@app.route("/admin/users/role/<int:uid>", methods=["POST"])
@admin_req
def admin_usr_role(uid):
    role = request.form.get("role","user")
    if role not in ROLE_RANK: abort(400)
    if uid == session.get("user_id") and role != "admin":
        return redirect("/admin/users")  # admin o'zini pastroq rolga tushirib qo'ymasin
    db_exec("UPDATE users SET role=? WHERE id=?", (role, uid), fetch=False)
    return redirect("/admin/users")

@app.route("/admin/users/toggle/<int:uid>",methods=["POST"])
@admin_req
def admin_usr_toggle(uid):
    db_exec("UPDATE users SET is_active=1-is_active WHERE id=?",(uid,),fetch=False)
    return redirect("/admin/users")

@app.route("/admin/users/del/<int:uid>",methods=["POST"])
@admin_req
def admin_usr_del(uid):
    if uid!=session.get("user_id"):
        db_exec("DELETE FROM users WHERE id=?",(uid,),fetch=False)
    return redirect("/admin/users")

@app.route("/admin/logs")
@admin_req
def admin_logs():
    pg=int(request.args.get("p",1)); pp=40
    tot=(q1("SELECT COUNT(*) c FROM access_logs") or {}).get("c",0)
    logs=db_exec("SELECT * FROM access_logs ORDER BY visited_at DESC LIMIT ? OFFSET ?",(pp,(pg-1)*pp)) or []
    rows="".join(f"""<tr>
      <td><span class="bx xp">{l['mode']}</span></td>
      <td><code style="font-size:.73rem">{l['ip_address']}</code></td>
      <td style="max-width:200px;overflow:hidden;text-overflow:ellipsis;font-size:.75rem">{l['path']}</td>
      <td><span class="bx {'xg' if l['status_code']==200 else 'xr'}">{l['status_code']}</span></td>
      <td class="tm" style="font-size:.73rem">{hsize(l['bytes_served'] or 0)}</td>
      <td class="tm" style="font-size:.73rem">{str(l['visited_at'])[:16]}</td>
    </tr>""" for l in logs)
    pages=max(1,(tot+pp-1)//pp)
    pager="".join(f'<a href="/admin/logs?p={i}" class="btn {"bp" if i==pg else "bgh"} bsm">{i}</a>' for i in range(max(1,pg-3),min(pages+1,pg+4)))
    body=f"""<h2 style="color:#fff;margin-bottom:14px">📋 Kirish loglari</h2>
    <div class="card" style="padding:0"><div class="tw">
      <table><thead><tr><th>Rejim</th><th>IP</th><th>Yo'l</th><th>Status</th><th>Hajm</th><th>Vaqt</th></tr></thead>
      <tbody>{rows}</tbody></table></div></div>
    <div class="fl mt" style="gap:5px">{pager}</div>"""
    return _pg("Kirish loglari",body,"logs")

@app.route("/admin/blocked")
@admin_req
def admin_blocked():
    bls=db_exec("SELECT * FROM blocked_ips ORDER BY blocked_at DESC") or []
    cutoff=(datetime.now()-timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
    fails=db_exec("SELECT ip_address,COUNT(*) cnt,MAX(attempt_at) last FROM failed_logins WHERE attempt_at>? GROUP BY ip_address ORDER BY cnt DESC LIMIT 15",(cutoff,)) or []
    rows="".join(f"""<tr>
      <td><code>{b['ip_address']}</code></td><td>{b.get('reason','—')}</td>
      <td class="tm" style="font-size:.75rem">{str(b['blocked_at'])[:16]}</td>
      <td class="tm" style="font-size:.75rem">{str(b.get('unblock_at','∞'))[:16] if b.get('unblock_at') else '∞'}</td>
      <td><form method="POST" action="/admin/blocked/del/{b['id']}">{csrf_field()}
        <button class="btn bg bsm">✓ Ochish</button></form></td>
    </tr>""" for b in bls)
    fr="".join(f"<tr><td><code>{r['ip_address']}</code></td><td>{r['cnt']}</td><td class='tm' style='font-size:.74rem'>{str(r['last'])[:16]}</td></tr>" for r in fails)
    body=f"""
    <div class="fl mb"><h2 style="color:#fff">🚫 Bloklangan IP</h2>
      <form method="POST" action="/admin/blocked/add" style="margin-left:auto;display:flex;gap:7px">{csrf_field()}
        <input name="ip" placeholder="IP manzil" style="padding:6px 10px;background:var(--bg);
          border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem;width:150px">
        <input name="reason" placeholder="Sabab" style="padding:6px 10px;background:var(--bg);
          border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem">
        <button class="btn br">+ Bloklash</button>
      </form>
    </div>
    <div class="g g2">
      <div class="card" style="padding:0"><div class="tw">
        <table><thead><tr><th>IP</th><th>Sabab</th><th>Bloklangan</th><th>Muddat</th><th>Amal</th></tr></thead>
        <tbody>{rows or '<tr><td colspan=5 style="text-align:center;color:var(--mt);padding:16px">Bloklangan IP yo\'q</td></tr>'}</tbody></table>
      </div></div>
      <div class="card"><h3>So'nggi xato urinishlar (1 soat)</h3>
        <div class="tw"><table><thead><tr><th>IP</th><th>Urinishlar</th><th>Oxirgi</th></tr></thead>
        <tbody>{fr or '<tr><td colspan=3 style="text-align:center;color:var(--mt);padding:14px">Hali yo\'q</td></tr>'}</tbody></table></div>
      </div>
    </div>"""
    return _pg("Bloklangan IPlar",body,"blocked")

@app.route("/admin/blocked/add",methods=["POST"])
@admin_req
def admin_block_add():
    ip=request.form.get("ip","").strip()
    reason=request.form.get("reason","Admin tomonidan bloklangan")
    if ip: db_exec("INSERT OR IGNORE INTO blocked_ips (ip_address,reason) VALUES (?,?)",(ip,reason),fetch=False)
    return redirect("/admin/blocked")

@app.route("/admin/blocked/del/<int:bid>",methods=["POST"])
@admin_req
def admin_unblock(bid):
    db_exec("DELETE FROM blocked_ips WHERE id=?",(bid,),fetch=False)
    return redirect("/admin/blocked")

@app.route("/admin/server/toggle", methods=["POST"])
@admin_req
def admin_server_toggle():
    cur = get_setting("server_enabled", "1")
    set_setting("server_enabled", "0" if cur == "1" else "1")
    return redirect(request.referrer or "/modes")

@app.route("/admin/bandwidth")
@admin_req
def admin_bandwidth():
    dy=db_exec("SELECT log_date,SUM(bytes_used) tot FROM bandwidth_log GROUP BY log_date ORDER BY log_date DESC LIMIT 30") or []
    ub=db_exec("SELECT username,bandwidth_limit_mb,bandwidth_used_mb FROM users ORDER BY bandwidth_used_mb DESC") or []
    dr="".join(f"<tr><td>{r['log_date']}</td><td>{hsize(r['tot'] or 0)}</td></tr>" for r in dy)
    ur="".join(f"""<tr><td>{u['username']}</td>
      <td>{u['bandwidth_used_mb']:.1f} MB</td>
      <td>{u['bandwidth_limit_mb'] or '∞'} MB</td>
      <td><div style="background:var(--brd);border-radius:3px;height:7px;overflow:hidden">
        <div style="background:var(--ac);height:100%;width:{min(100,int((u['bandwidth_used_mb']/(u['bandwidth_limit_mb'] or 9999))*100))}%"></div>
      </div></td></tr>""" for u in ub)
    body=f"""<h2 style="color:#fff;margin-bottom:14px">📊 Bandwidth</h2>
    <div class="g g2">
      <div class="card"><h3>Kunlik trafik</h3>
        <div class="tw"><table><thead><tr><th>Kun</th><th>Trafik</th></tr></thead>
        <tbody>{dr or '<tr><td colspan=2 style="text-align:center;color:var(--mt);padding:14px">Ma\'lumot yo\'q</td></tr>'}</tbody></table></div>
      </div>
      <div class="card"><h3>Foydalanuvchilar</h3>
        <div class="tw"><table><thead><tr><th>User</th><th>Ishlatilgan</th><th>Limit</th><th>Holat</th></tr></thead>
        <tbody>{ur}</tbody></table></div>
      </div>
    </div>"""
    return _pg("Bandwidth",body,"bw")

# ── Server monitoring (CPU/RAM/Disk/Tarmoq) ──────────────
@app.route("/admin/monitor")
@admin_req
def admin_monitor():
    warn = "" if PSUTIL_OK else '<div class="al al-er">psutil o\'rnatilmagan: <code>pip install psutil</code></div>'
    body = f"""
    <div class="fl mb"><h2 style="color:#fff">📟 Server Monitoring</h2>
      <span class="bx xg mla" id="live-badge">● Jonli</span></div>
    {warn}
    <div class="mongrid">
      <div class="stat"><div class="v" id="m-cpu">—</div><div class="l">CPU %</div>
        <div class="monbar"><div class="monfill" id="b-cpu" style="width:0%;background:var(--ac)"></div></div></div>
      <div class="stat"><div class="v" id="m-mem">—</div><div class="l">RAM ishlatilgan</div>
        <div class="monbar"><div class="monfill" id="b-mem" style="width:0%;background:var(--gr)"></div></div></div>
      <div class="stat"><div class="v" id="m-disk">—</div><div class="l">Disk ishlatilgan</div>
        <div class="monbar"><div class="monfill" id="b-disk" style="width:0%;background:var(--yl)"></div></div></div>
      <div class="stat"><div class="v" id="m-uptime">—</div><div class="l">Server ishlagan vaqt</div></div>
    </div>
    <div class="card mt"><h3>Tarmoq trafigi (server ishga tushganidan buyon)</h3>
      <div class="g g2">
        <div><p class="tm" style="font-size:.8rem">⬆ Yuborilgan</p><p style="font-size:1.3rem;color:var(--ac)" id="m-sent">—</p></div>
        <div><p class="tm" style="font-size:.8rem">⬇ Qabul qilingan</p><p style="font-size:1.3rem;color:var(--gr)" id="m-recv">—</p></div>
      </div>
    </div>
    <script>
    function fmtMin(m){{
      if(m<60) return m.toFixed(0)+' daqiqa';
      var h=Math.floor(m/60), mm=Math.round(m%60);
      return h+' soat '+mm+' daqiqa';
    }}
    function poll(){{
      fetch('/api/monitor').then(r=>r.json()).then(d=>{{
        if(d.error){{document.getElementById('m-cpu').textContent='N/A';return;}}
        document.getElementById('m-cpu').textContent=d.cpu.toFixed(1)+'%';
        document.getElementById('b-cpu').style.width=d.cpu+'%';
        document.getElementById('m-mem').textContent=d.mem_used+'/'+d.mem_total+' GB';
        document.getElementById('b-mem').style.width=d.mem_percent+'%';
        document.getElementById('m-disk').textContent=d.disk_used+'/'+d.disk_total+' GB';
        document.getElementById('b-disk').style.width=d.disk_percent+'%';
        document.getElementById('m-uptime').textContent=fmtMin(d.uptime_min);
        document.getElementById('m-sent').textContent=d.net_sent+' MB';
        document.getElementById('m-recv').textContent=d.net_recv+' MB';
      }}).catch(()=>{{document.getElementById('live-badge').textContent='● Uzildi';
        document.getElementById('live-badge').className='bx xr mla';}});
    }}
    poll(); setInterval(poll,2000);
    </script>"""
    return _pg("Monitoring", body, "monitor")

@app.route("/api/monitor")
@admin_req
def api_monitor():
    if not PSUTIL_OK:
        return jsonify({"error":"psutil o'rnatilmagan"})
    cpu = psutil.cpu_percent(interval=0.2)
    mem = psutil.virtual_memory()
    disk = psutil.disk_usage(os.getcwd())
    net = psutil.net_io_counters()
    return jsonify({
        "cpu": cpu,
        "mem_percent": mem.percent,
        "mem_used": round(mem.used/1073741824,1),
        "mem_total": round(mem.total/1073741824,1),
        "disk_percent": disk.percent,
        "disk_used": round(disk.used/1073741824,1),
        "disk_total": round(disk.total/1073741824,1),
        "net_sent": round(net.bytes_sent/1048576,1),
        "net_recv": round(net.bytes_recv/1048576,1),
        "uptime_min": round((time.time()-PROCESS_START)/60,1)
    })

# ── Sozlamalar + Backup/Restore + Telegram 2FA ───────────────
@app.route("/admin/settings", methods=["GET","POST"])
@admin_req
def admin_settings():
    suc=None
    if request.method=="POST":
        set_setting("tg_enabled", "1" if request.form.get("tg_enabled") else "0")
        set_setting("tg_token", request.form.get("tg_token","").strip())
        set_setting("tg_chat", request.form.get("tg_chat","").strip())
        set_setting("site_title", request.form.get("site_title","SrvManager").strip() or "SrvManager")
        suc="Sozlamalar saqlandi"
    tg_enabled = get_setting("tg_enabled","0")=="1"
    tg_token = get_setting("tg_token", CFG["TELEGRAM_TOKEN"])
    tg_chat  = get_setting("tg_chat", CFG["TELEGRAM_CHAT_ID"])
    site_title = get_setting("site_title","SrvManager")
    api_keys = db_exec("SELECT ak.*,u.username FROM api_keys ak JOIN users u ON ak.user_id=u.id WHERE ak.revoked=0 ORDER BY ak.created_at DESC") or []
    ak_rows = "".join(f"""<tr><td>{k['username']}</td><td>{k.get('name') or '—'}</td>
      <td><code>{k['key_prefix']}…</code></td><td class="tm" style="font-size:.74rem">{str(k['created_at'])[:16]}</td>
      <td><form method="POST" action="/admin/apikeys/revoke/{k['id']}">{csrf_field()}
        <button class="btn br bsm">🗑 Bekor qilish</button></form></td></tr>""" for k in api_keys)
    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">⚙️ Sozlamalar</h2>
    <a href="/admin/backend/logs" class="btn bgh bsm">🐍 Backend loglari</a>
    <div class="card"><h3>🔔 Telegram bildirishnomalar / 2FA</h3>
      <p class="tm mb" style="font-size:.79rem">Yangi login, bloklangan IP, ro'yxatdan o'tish, fayl yuklash va 2FA tasdiqlash kodlari uchun.
      Bot yaratish uchun @BotFather ga, chat ID olish uchun @userinfobot ga yozing. Har bir foydalanuvchi
      o'zining shaxsiy 2FA chat ID sini <a href="/profile">Profil</a> sahifasida sozlashi mumkin.</p>
      <form method="POST">{csrf_field()}
        <label style="display:flex;gap:8px;align-items:center;margin-bottom:12px">
          <input type="checkbox" name="tg_enabled" {'checked' if tg_enabled else ''} style="width:auto">
          Bildirishnomalarni yoqish
        </label>
        <div class="g g2">
          <div class="fld"><label>Bot Token</label><input name="tg_token" value="{tg_token}" placeholder="123456:ABC-DEF..."></div>
          <div class="fld"><label>Standart Chat ID</label><input name="tg_chat" value="{tg_chat}" placeholder="123456789"></div>
        </div>
        <div class="fld"><label>Sayt nomi</label><input name="site_title" value="{site_title}"></div>
        <button class="btn bp">💾 Saqlash</button>
      </form>
    </div>
    <div class="card"><h3>🔑 API kalitlari (barcha foydalanuvchilar)</h3>
      <p class="tm mb" style="font-size:.79rem">Foydalanuvchilar o'z kalitlarini <a href="/profile">Profil</a> sahifasidan yaratadi.
      Bu yerda barcha faol kalitlarni ko'rish va bekor qilish mumkin.</p>
      <div class="tw"><table><thead><tr><th>Foydalanuvchi</th><th>Nomi</th><th>Prefiks</th><th>Yaratilgan</th><th>Amal</th></tr></thead>
      <tbody>{ak_rows or '<tr><td colspan=5 style="text-align:center;color:var(--mt);padding:14px">Hali API kalit yo\'q</td></tr>'}</tbody></table></div>
    </div>
    <div class="card"><h3>💾 Backup / Restore</h3>
      <p class="tm mb" style="font-size:.8rem">Butun bazani (foydalanuvchilar, havolalar, loyihalar, loglar) zaxira nusxa qiling yoki tiklang.</p>
      <a href="/admin/backup/download" class="btn bg">⬇ Backup yuklab olish</a>
      <form method="POST" action="/admin/backup/restore" enctype="multipart/form-data" style="margin-top:16px" onsubmit="return confirm('Joriy baza almashtiriladi va qaytarib bo\\'lmaydi. Davom etasizmi?')">{csrf_field()}
        <div class="fld"><label>Backup faylni tanlang (.db)</label><input type="file" name="backup_file" accept=".db" required></div>
        <button class="btn br">⬆ Tiklash (Restore)</button>
      </form>
    </div>"""
    return _pg("Sozlamalar", body, "settings", flash=suc, ftype="ok")

@app.route("/admin/apikeys/revoke/<int:kid>", methods=["POST"])
@admin_req
def admin_apikey_revoke(kid):
    db_exec("UPDATE api_keys SET revoked=1 WHERE id=?", (kid,), fetch=False)
    return redirect("/admin/settings")

@app.route("/admin/backup/download")
@admin_req
def admin_backup_download():
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_name = f"backup_{ts}.db"
    backup_path = Path(CFG["DB_FILE"]).parent / backup_name
    shutil.copy(CFG["DB_FILE"], backup_path)
    return send_file(str(backup_path), as_attachment=True, download_name=backup_name)

@app.route("/admin/backup/restore", methods=["POST"])
@admin_req
def admin_backup_restore():
    f = request.files.get("backup_file")
    if f and f.filename.endswith(".db"):
        safety = Path(CFG["DB_FILE"]).parent / f"pre_restore_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
        try: shutil.copy(CFG["DB_FILE"], safety)
        except: pass
        f.save(CFG["DB_FILE"])
    return redirect("/admin/settings")

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║              2FA TASDIQLASH BOSQICHI (Telegram bir martalik kod)         ║
# ║  ESLATMA: login() funksiyasi hozircha to'g'ridan-to'g'ri sessiya         ║
# ║  ochadi. To'liq 2FA ishlashi uchun login()dagi finalize qismini          ║
# ║  quyidagi bitta shart bilan almashtirish kerak (pastdagi izohga qarang). ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/login/verify", methods=["GET","POST"])
def login_verify():
    pending_uid = session.get("_pending_2fa_uid")
    if not pending_uid:
        return redirect("/login")
    err = None
    if request.method == "POST":
        code = request.form.get("code","").strip()
        if verify_2fa_code(pending_uid, code):
            user = q1("SELECT * FROM users WHERE id=?", (pending_uid,))
            session.pop("_pending_2fa_uid", None)
            finalize_login(user, get_ip())
            return redirect("/dashboard")
        err = "Kod noto'g'ri yoki muddati o'tgan"
    f = f"""
    <form method="POST">{csrf_field()}
      <div class="fld"><label>Telegramga yuborilgan 6 xonali kod</label>
        <input name="code" required maxlength="6" autofocus placeholder="000000"></div>
      <button class="btn bp" style="width:100%">Tasdiqlash</button>
    </form>"""
    return _auth_pg("Ikki bosqichli tasdiqlash", f, err)

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║              TASHQI API (Bearer token) — REST endpointlar                ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/api/v1/links", methods=["GET","POST"])
@api_key_req
def api_links():
    uid = request.api_user_id
    if request.method == "GET":
        rows = db_exec("SELECT id,token,mode,label,is_active,visit_count,created_at FROM links WHERE owner_id=? ORDER BY created_at DESC",(uid,)) or []
        return jsonify({"links": rows})
    d = request.get_json(silent=True) or {}
    mode = d.get("mode","private")
    if mode not in ("private","lan","global"): return jsonify({"error":"noto'g'ri mode"}), 400
    tok = gtok()
    db_exec("INSERT INTO links (token,mode,label,target_path,owner_id) VALUES (?,?,?,?,?)",
            (tok, mode, d.get("label",""), d.get("target_path",""), uid), fetch=False)
    return jsonify({"ok": True, "token": tok})

@app.route("/api/v1/files", methods=["GET"])
@api_key_req
def api_files():
    uid = request.api_user_id
    rows = db_exec("SELECT uuid,original_name,file_size_bytes,is_public,download_count,created_at FROM files WHERE owner_id=? ORDER BY created_at DESC",(uid,)) or []
    return jsonify({"files": rows})

@app.route("/api/v1/projects", methods=["GET"])
@api_key_req
def api_projects():
    uid = request.api_user_id
    rows = db_exec("SELECT uuid,name,current_version,is_public,updated_at FROM projects WHERE owner_id=? ORDER BY updated_at DESC",(uid,)) or []
    return jsonify({"projects": rows})

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     PROFIL (2FA, API kalitlar, shaxsiy sozlamalar)       ║
# ╚══════════════════════════════════════════════════════════════════════════╝
@app.route("/profile",methods=["GET","POST"])
@user_req
def profile():
    uid=session["user_id"]; err=suc=None
    if uid == 0:  # guest — profilga ega emas
        return redirect("/dashboard")
    if request.method=="POST":
        action = request.form.get("_action","update")
        if action == "update":
            e=request.form.get("email","").strip()
            tg_chat_id = request.form.get("tg_chat_id","").strip()
            req2fa = 1 if request.form.get("require_2fa") else 0
            op=request.form.get("old_password",""); np=request.form.get("new_password",""); cp=request.form.get("confirm_password","")
            user=q1("SELECT * FROM users WHERE id=?",(uid,))
            if np:
                if not check_password_hash(user["password_hash"],op): err="Joriy parol noto'g'ri"
                elif np!=cp: err="Yangi parollar mos kelmadi"
                elif len(np)<6: err="Kamida 6 ta belgi"
                else:
                    db_exec("UPDATE users SET email=?,password_hash=?,tg_chat_id=?,require_2fa=? WHERE id=?",
                            (e,generate_password_hash(np),tg_chat_id,req2fa,uid),fetch=False)
                    suc="Parol va sozlamalar yangilandi"
            else:
                db_exec("UPDATE users SET email=?,tg_chat_id=?,require_2fa=? WHERE id=?",(e,tg_chat_id,req2fa,uid),fetch=False)
                suc="Sozlamalar yangilandi"
        elif action == "new_api_key" and role_rank(session.get("role")) >= ROLE_RANK["user"]:
            raw = new_api_key(uid, request.form.get("key_name","API kalit"))
            suc = f"Yangi API kalit (faqat shu safar ko'rsatiladi, saqlab qo'ying): {raw}"
    user=q1("SELECT * FROM users WHERE id=?",(uid,))
    my_keys = db_exec("SELECT * FROM api_keys WHERE user_id=? AND revoked=0 ORDER BY created_at DESC",(uid,)) or []
    keys_html = "".join(f"""<tr><td>{k.get('name') or '—'}</td><td><code>{k['key_prefix']}…</code></td>
      <td class="tm" style="font-size:.74rem">{str(k['created_at'])[:16]}</td>
      <td><form method="POST" action="/profile/apikey/revoke/{k['id']}">{csrf_field()}
        <button class="btn br bsm">🗑</button></form></td></tr>""" for k in my_keys)
    form=f"""<form method="POST">{csrf_field()}<input type="hidden" name="_action" value="update">
      <div class="fld"><label>Username</label><input value="{user['username']}" disabled style="opacity:.5"></div>
      <div class="fld"><label>Email</label><input name="email" value="{user.get('email','')}" type="email"></div>
      <div class="fld"><label>Telegram Chat ID (2FA kodlari shu yerga yuboriladi)</label>
        <input name="tg_chat_id" value="{user.get('tg_chat_id') or ''}" placeholder="@userinfobot orqali oling"></div>
      <label style="display:flex;gap:8px;align-items:center;margin-bottom:12px">
        <input type="checkbox" name="require_2fa" {'checked' if user.get('require_2fa') else ''} style="width:auto">
        Kirishda Telegram orqali 2FA talab qilish
      </label>
      <div class="fld"><label>Joriy parol</label><input name="old_password" type="password"></div>
      <div class="g g2">
        <div class="fld"><label>Yangi parol</label><input name="new_password" type="password"></div>
        <div class="fld"><label>Tasdiqlash</label><input name="confirm_password" type="password"></div>
      </div>
      <button class="btn bp">Saqlash</button></form>"""
    api_form = f"""<form method="POST">{csrf_field()}<input type="hidden" name="_action" value="new_api_key">
      <div class="row"><div class="fld" style="flex:1"><label>Yangi API kalit nomi</label>
        <input name="key_name" placeholder="Masalan: CI/CD skripti"></div>
      <button class="btn bp">+ Yaratish</button></div></form>
      <div class="tw mt"><table><thead><tr><th>Nomi</th><th>Prefiks</th><th>Yaratilgan</th><th>Amal</th></tr></thead>
      <tbody>{keys_html or '<tr><td colspan=4 style="text-align:center;color:var(--mt);padding:12px">Hali API kalit yo\'q</td></tr>'}</tbody></table></div>
      <p class="tm mt" style="font-size:.76rem">Bearer token sifatida ishlating: <code>Authorization: Bearer &lt;kalit&gt;</code>
      — masalan <code>GET /api/v1/links</code>, <code>/api/v1/files</code>, <code>/api/v1/projects</code>.</p>"""
    body = f"""
    <div class="card" style="max-width:520px"><h3>Profil</h3>{form}</div>
    <div class="card" style="max-width:520px"><h3>🔑 API kalitlarim</h3>{api_form}</div>"""
    return _pg("Profilim",body,"profile",flash=suc or err,ftype="ok" if suc else "er")

@app.route("/profile/apikey/revoke/<int:kid>", methods=["POST"])
@user_req
def profile_apikey_revoke(kid):
    db_exec("UPDATE api_keys SET revoked=1 WHERE id=? AND user_id=?", (kid, session["user_id"]), fetch=False)
    return redirect("/profile")

@app.errorhandler(403)
def e403(e):
    return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
    <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center}}</style>
    </head><body><div><p style="font-size:2.5rem">🚫</p>
    <h1 style="color:var(--rd);margin:10px 0">403 — Kirish taqiqlangan</h1>
    <a href="/" class="btn bgh mt">← Asosiy</a></div></body></html>""",403

@app.errorhandler(404)
def e404(e):
    return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
    <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center}}</style>
    </head><body><div><p style="font-size:2.5rem">🔍</p>
    <h1 style="color:var(--mt);margin:10px 0">404 — Topilmadi</h1>
    <a href="/" class="btn bgh mt">← Asosiy</a></div></body></html>""",404

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║        YANGI FUNKSIYALAR: Domain, Chat, PWA, Team, Audit, TODO, ...     ║
# ╚══════════════════════════════════════════════════════════════════════════╝

# ── Audit Trail — barcha muhim harakatlarni qayd qilish ───────────────────
def audit(action, target_type=None, target_id=None, details=None):
    """Muhim amallarni audit_log jadvaliga yozadi."""
    try:
        uid = session.get("user_id")
        uname = session.get("username", "")
        ip = get_ip()
        db_exec("INSERT INTO audit_log (user_id,username,action,target_type,target_id,details,ip_address) "
                "VALUES (?,?,?,?,?,?,?)",
                (uid, uname, action, target_type, str(target_id) if target_id else None,
                 (details or "")[:500], ip), fetch=False)
    except Exception:
        pass



# ── IP Whitelist middleware ────────────────────────────────────────────────
@app.before_request
def _check_ip_whitelist():
    """Agar IP whitelist yoqilgan bo'lsa, faqat ro'yxatdagi IP larni o'tkazadi."""
    if get_setting("ip_whitelist_enabled", "0") != "1":
        return None
    if request.path in ("/login", "/logout") or request.path.startswith("/static"):
        return None
    if session.get("admin"):
        return None
    ip = get_ip()
    allowed_ip = q1("SELECT id FROM ip_whitelist WHERE ip_address=?", (ip,))
    if not allowed_ip:
        return f"""<!DOCTYPE html><html><head><meta charset=UTF-8>
        <style>{CSS} body{{display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center}}</style>
        </head><body><div><p style="font-size:2.5rem">🔒</p>
        <h1 style="color:var(--rd);margin:10px 0">Kirish cheklangan</h1>
        <p class="tm">Sizning IP ({ip}) ruxsat ro'yxatida yo'q.</p>
        <a href="/login" class="btn bgh mt">Admin sifatida kirish</a>
        </div></body></html>""", 403
    return None



# ── Admin: IP Whitelist boshqaruvi ────────────────────────────────────────
@app.route("/admin/ip-whitelist", methods=["GET", "POST"])
@admin_req
def admin_ip_whitelist():
    suc = None
    if request.method == "POST":
        action = request.form.get("_action", "add")
        if action == "add":
            ip = request.form.get("ip", "").strip()
            label = request.form.get("label", "").strip()
            if ip:
                db_exec("INSERT OR IGNORE INTO ip_whitelist (ip_address,label,added_by) VALUES (?,?,?)",
                        (ip, label, session["user_id"]), fetch=False)
                audit("ip_whitelist_add", "ip", ip, label)
                suc = f"IP qo'shildi: {ip}"
        elif action == "delete":
            wid = request.form.get("wid")
            db_exec("DELETE FROM ip_whitelist WHERE id=?", (wid,), fetch=False)
            audit("ip_whitelist_remove", "ip", wid)
            suc = "IP o'chirildi"
        elif action == "toggle":
            cur = get_setting("ip_whitelist_enabled", "0")
            set_setting("ip_whitelist_enabled", "0" if cur == "1" else "1")
            suc = "IP whitelist holati o'zgartirildi"
    wl_on = get_setting("ip_whitelist_enabled", "0") == "1"
    ips = db_exec("SELECT * FROM ip_whitelist ORDER BY created_at DESC") or []
    rows = "".join(f"""<tr><td><code>{ip['ip_address']}</code></td><td>{ip.get('label') or '—'}</td>
      <td class="tm" style="font-size:.74rem">{str(ip['created_at'])[:16]}</td>
      <td><form method="POST">{csrf_field()}<input type="hidden" name="_action" value="delete">
        <input type="hidden" name="wid" value="{ip['id']}">
        <button class="btn br bsm">🗑</button></form></td></tr>""" for ip in ips)
    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">🔒 IP Whitelist</h2>
    <div class="card">
      <div class="fl mb">
        <span class="bx {'xg' if wl_on else 'xm'}">{'Yoqilgan' if wl_on else "O'chirilgan"}</span>
        <form method="POST" style="margin-left:auto">{csrf_field()}
          <input type="hidden" name="_action" value="toggle">
          <button class="btn {'br' if wl_on else 'bg'} bsm">{"🔴 O'chirish" if wl_on else "🟢 Yoqish"}</button>
        </form>
      </div>
      <p class="tm mb" style="font-size:.79rem">Yoqilganda faqat ro'yxatdagi IP lar saytga kira oladi. Admin har doim kirishi mumkin.</p>
      <form method="POST" class="row mb">{csrf_field()}<input type="hidden" name="_action" value="add">
        <input name="ip" placeholder="IP manzil (masalan: 192.168.1.10)" required style="flex:1;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem">
        <input name="label" placeholder="Izoh" style="flex:1;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem">
        <button class="btn bp bsm">+ Qo'shish</button>
      </form>
      <div class="tw"><table><thead><tr><th>IP</th><th>Izoh</th><th>Qo'shilgan</th><th>Amal</th></tr></thead>
      <tbody>{rows or '<tr><td colspan=4 style="text-align:center;color:var(--mt);padding:14px">Royxat bosh</td></tr>'}</tbody></table></div>
    </div>"""
    return _pg("IP Whitelist", body, "ipwl", flash=suc, ftype="ok")



# ── Custom Domain / Subdomain ─────────────────────────────────────────────
@app.route("/admin/domains", methods=["GET", "POST"])
@admin_req
def admin_domains():
    suc = None
    if request.method == "POST":
        action = request.form.get("_action", "add")
        if action == "add":
            puuid = request.form.get("project_uuid", "").strip()
            domain = request.form.get("domain", "").strip().lower()
            proj = q1("SELECT id FROM projects WHERE uuid=?", (puuid,))
            if proj and domain:
                db_exec("INSERT OR IGNORE INTO custom_domains (project_id,domain,created_by) VALUES (?,?,?)",
                        (proj["id"], domain, session["user_id"]), fetch=False)
                audit("domain_add", "domain", domain)
                suc = f"Domain qo'shildi: {domain}"
        elif action == "delete":
            did = request.form.get("did")
            db_exec("DELETE FROM custom_domains WHERE id=?", (did,), fetch=False)
            suc = "Domain o'chirildi"
        elif action == "toggle":
            did = request.form.get("did")
            db_exec("UPDATE custom_domains SET is_active=1-is_active WHERE id=?", (did,), fetch=False)
            suc = "Domain holati o'zgartirildi"
    domains = db_exec("SELECT d.*,p.name as pname,p.uuid as puuid FROM custom_domains d LEFT JOIN projects p ON d.project_id=p.id ORDER BY d.created_at DESC") or []
    projs = db_exec("SELECT uuid,name FROM projects ORDER BY name") or []
    po = "".join(f'<option value="{p["uuid"]}">{p["name"]}</option>' for p in projs)
    rows = "".join(f"""<tr>
      <td><code style="color:var(--ac)">{d['domain']}</code></td>
      <td>{d.get('pname') or '—'}</td>
      <td><span class="bx {'xg' if d['is_active'] else 'xr'}">{'Faol' if d['is_active'] else "O'chiq"}</span></td>
      <td class="fl">
        <form method="POST">{csrf_field()}<input type="hidden" name="_action" value="toggle"><input type="hidden" name="did" value="{d['id']}">
          <button class="btn bgh bsm">{'⏸' if d['is_active'] else '▶️'}</button></form>
        <form method="POST">{csrf_field()}<input type="hidden" name="_action" value="delete"><input type="hidden" name="did" value="{d['id']}">
          <button class="btn br bsm">🗑</button></form>
      </td></tr>""" for d in domains)
    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">🌐 Custom Domain / Subdomain</h2>
    <div class="card">
      <p class="tm mb" style="font-size:.79rem">Har loyihaga o'z domain/subdomain berish. DNS A yozuvini server IP ga yo'naltiring.
      Loyiha domeni orqali ochilganda avtomatik preview sahifasiga yo'naltiriladi.</p>
      <form method="POST" class="row mb">{csrf_field()}<input type="hidden" name="_action" value="add">
        <select name="project_uuid" required style="flex:1;padding:7px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx)"><option value="">Loyiha tanlang</option>{po}</select>
        <input name="domain" placeholder="masalan: mysite.example.com" required style="flex:2;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx);font-size:.82rem">
        <button class="btn bp bsm">+ Qo'shish</button>
      </form>
      <div class="tw"><table><thead><tr><th>Domain</th><th>Loyiha</th><th>Holat</th><th>Amallar</th></tr></thead>
      <tbody>{rows or '<tr><td colspan=4 style="text-align:center;color:var(--mt);padding:14px">Hali domain yoq</td></tr>'}</tbody></table></div>
    </div>"""
    return _pg("Domenlar", body, "domains", flash=suc, ftype="ok")

# Domain orqali kelgan so'rovlarni loyiha preview ga yo'naltirish
@app.before_request
def _check_custom_domain():
    host = request.host.split(":")[0].lower()
    if host in ("127.0.0.1", "localhost", "0.0.0.0"):
        return None
    dom = q1("SELECT d.*,p.uuid FROM custom_domains d JOIN projects p ON d.project_id=p.id WHERE d.domain=? AND d.is_active=1", (host,))
    if dom and request.path == "/":
        return redirect(f"/preview/{dom['uuid']}")
    return None



# ── Jamoa/Team tizimi ─────────────────────────────────────────────────────
@app.route("/projects/<puuid>/team", methods=["GET", "POST"])
@user_req
def project_team(puuid):
    proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        abort(404)
    is_owner = proj["owner_id"] == session["user_id"]
    if not is_owner and not session.get("admin"):
        abort(403)
    suc = err = None
    if request.method == "POST":
        action = request.form.get("_action", "invite")
        if action == "invite":
            username = request.form.get("username", "").strip()
            role = request.form.get("role", "viewer")
            if role not in ("viewer", "editor"):
                role = "viewer"
            user = q1("SELECT id FROM users WHERE username=?", (username,))
            if not user:
                err = "Foydalanuvchi topilmadi"
            elif user["id"] == proj["owner_id"]:
                err = "Loyiha egasini qo'shish shart emas"
            else:
                db_exec("INSERT OR REPLACE INTO project_teams (project_id,user_id,role,invited_by) VALUES (?,?,?,?)",
                        (proj["id"], user["id"], role, session["user_id"]), fetch=False)
                audit("team_invite", "project", puuid, f"{username} -> {role}")
                suc = f"{username} jamoga qo'shildi ({role})"
        elif action == "remove":
            tid = request.form.get("tid")
            db_exec("DELETE FROM project_teams WHERE id=? AND project_id=?", (tid, proj["id"]), fetch=False)
            suc = "Foydalanuvchi jamoadan chiqarildi"
    members = db_exec("SELECT t.*,u.username,u.email FROM project_teams t JOIN users u ON t.user_id=u.id WHERE t.project_id=? ORDER BY t.created_at", (proj["id"],)) or []
    rows = "".join(f"""<tr><td>{m['username']}</td><td>{m.get('email','')}</td>
      <td><span class="bx {'xb' if m['role']=='editor' else 'xm'}">{m['role']}</span></td>
      <td><form method="POST">{csrf_field()}<input type="hidden" name="_action" value="remove">
        <input type="hidden" name="tid" value="{m['id']}"><button class="btn br bsm">🗑</button></form></td></tr>""" for m in members)
    import html as hm
    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">🧑‍🤝‍🧑 Jamoa — {hm.escape(proj['name'])}</h2>
    <div class="card">
      <form method="POST" class="row mb">{csrf_field()}<input type="hidden" name="_action" value="invite">
        <input name="username" placeholder="Username" required style="flex:1;padding:7px 10px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx)">
        <select name="role" style="padding:7px;background:var(--bg);border:1px solid var(--brd);border-radius:6px;color:var(--tx)">
          <option value="viewer">Viewer</option><option value="editor">Editor</option></select>
        <button class="btn bp bsm">+ Taklif qilish</button>
      </form>
      <div class="tw"><table><thead><tr><th>Foydalanuvchi</th><th>Email</th><th>Rol</th><th>Amal</th></tr></thead>
      <tbody>{rows or '<tr><td colspan=4 style="text-align:center;color:var(--mt);padding:14px">Hali jamoa azosi yoq</td></tr>'}</tbody></table></div>
    </div>
    <a href="/projects" class="btn bgh mt">← Loyihalar</a>"""
    return _pg("Jamoa", body, "projects", flash=suc or err, ftype="ok" if suc else "er")



# ── Real-time Chat (SSE - Server-Sent Events) ─────────────────────────────
@app.route("/api/chat/<puuid>/messages")
@user_req
def chat_messages(puuid):
    proj = q1("SELECT id FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        return jsonify({"messages": []})
    msgs = db_exec("SELECT * FROM chat_messages WHERE project_id=? ORDER BY id DESC LIMIT 50", (proj["id"],)) or []
    msgs.reverse()
    return jsonify({"messages": [{"id": m["id"], "username": m["username"], "message": m["message"],
                                   "created_at": str(m["created_at"])[:19]} for m in msgs]})

@app.route("/api/chat/<puuid>/send", methods=["POST"])
@user_req
def chat_send(puuid):
    proj = q1("SELECT id FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        return jsonify({"ok": False}), 404
    d = request.get_json() or {}
    msg = (d.get("message") or "").strip()[:500]
    if not msg:
        return jsonify({"ok": False, "error": "Xabar bo'sh"})
    db_exec("INSERT INTO chat_messages (project_id,user_id,username,message) VALUES (?,?,?,?)",
            (proj["id"], session["user_id"], session.get("username", ""), msg), fetch=False)
    return jsonify({"ok": True})



# ── PWA Generator ─────────────────────────────────────────────────────────
@app.route("/api/pwa/generate/<puuid>", methods=["POST"])
@user_req
@write_req
def pwa_generate(puuid):
    proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        return jsonify({"ok": False}), 404
    import html as hm
    name = proj["name"]
    # manifest.json
    manifest = json.dumps({
        "name": name, "short_name": name[:12], "start_url": ".", "display": "standalone",
        "background_color": "#0d0f18", "theme_color": "#7c6fff",
        "icons": [{"src": "icon-192.png", "sizes": "192x192", "type": "image/png"},
                  {"src": "icon-512.png", "sizes": "512x512", "type": "image/png"}]
    }, indent=2, ensure_ascii=False)
    # service-worker.js
    sw = """const CACHE='pwa-v1';const ASSETS=['/','/index.html'];
self.addEventListener('install',e=>e.waitUntil(caches.open(CACHE).then(c=>c.addAll(ASSETS))));
self.addEventListener('fetch',e=>e.respondWith(caches.match(e.request).then(r=>r||fetch(e.request))));"""
    # Fayllarni loyihaga yozamiz
    db_exec("INSERT INTO project_files (project_id,path,is_folder,content) VALUES (?,?,0,?) "
            "ON CONFLICT(project_id,path) DO UPDATE SET content=excluded.content,updated_at=datetime('now')",
            (proj["id"], "manifest.json", manifest), fetch=False)
    db_exec("INSERT INTO project_files (project_id,path,is_folder,content) VALUES (?,?,0,?) "
            "ON CONFLICT(project_id,path) DO UPDATE SET content=excluded.content,updated_at=datetime('now')",
            (proj["id"], "sw.js", sw), fetch=False)
    # index.html ga manifest va sw registratsiyasini qo'shamiz
    idx = q1("SELECT content FROM project_files WHERE project_id=? AND path='index.html'", (proj["id"],))
    if idx and idx.get("content"):
        html_content = idx["content"]
        if "manifest.json" not in html_content and "</head>" in html_content:
            pwa_tags = '  <link rel="manifest" href="manifest.json">\n  <meta name="theme-color" content="#7c6fff">\n'
            html_content = html_content.replace("</head>", pwa_tags + "</head>")
        if "sw.js" not in html_content and "</body>" in html_content:
            sw_reg = "  <script>if('serviceWorker' in navigator)navigator.serviceWorker.register('sw.js');</script>\n"
            html_content = html_content.replace("</body>", sw_reg + "</body>")
        db_exec("UPDATE project_files SET content=?,updated_at=datetime('now') WHERE project_id=? AND path='index.html'",
                (html_content, proj["id"]), fetch=False)
    audit("pwa_generate", "project", puuid)
    return jsonify({"ok": True, "files": ["manifest.json", "sw.js"]})



# ── TODO / Vazifalar ro'yxati ──────────────────────────────────────────────
@app.route("/api/todos/<puuid>", methods=["GET", "POST"])
@user_req
def api_todos(puuid):
    proj = q1("SELECT id FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        return jsonify({"todos": []})
    if request.method == "GET":
        todos = db_exec("SELECT * FROM project_todos WHERE project_id=? ORDER BY is_done, priority DESC, id DESC",
                        (proj["id"],)) or []
        return jsonify({"todos": todos})
    d = request.get_json() or {}
    title = (d.get("title") or "").strip()[:200]
    priority = d.get("priority", "normal")
    if priority not in ("low", "normal", "high"):
        priority = "normal"
    if not title:
        return jsonify({"ok": False, "error": "Sarlavha kerak"})
    new_id = db_exec("INSERT INTO project_todos (project_id,user_id,title,priority) VALUES (?,?,?,?)",
                     (proj["id"], session["user_id"], title, priority), fetch=False)
    return jsonify({"ok": True, "id": new_id})

@app.route("/api/todos/<puuid>/<int:tid>", methods=["PUT", "DELETE"])
@user_req
def api_todo_item(puuid, tid):
    proj = q1("SELECT id FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        abort(404)
    if request.method == "DELETE":
        db_exec("DELETE FROM project_todos WHERE id=? AND project_id=?", (tid, proj["id"]), fetch=False)
        return jsonify({"ok": True})
    d = request.get_json() or {}
    is_done = 1 if d.get("is_done") else 0
    completed_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S") if is_done else None
    db_exec("UPDATE project_todos SET is_done=?,completed_at=? WHERE id=? AND project_id=?",
            (is_done, completed_at, tid, proj["id"]), fetch=False)
    return jsonify({"ok": True})



# ── Rasm yuklash (muharrir ichida drag&drop) ───────────────────────────────
@app.route("/editor/upload-image/<puuid>", methods=["POST"])
@user_req
@write_req
def editor_upload_image(puuid):
    proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        return jsonify({"ok": False}), 404
    f = request.files.get("image")
    if not f or not f.filename:
        return jsonify({"ok": False, "error": "Fayl tanlanmadi"})
    ext = Path(f.filename).suffix.lower()
    if ext not in (".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp", ".ico"):
        return jsonify({"ok": False, "error": "Ruxsat etilmagan format"})
    safe_name = secure_filename(f.filename)
    stored = f"{uuid.uuid4().hex[:8]}_{safe_name}"
    dest = FILES_PATH / stored
    f.save(str(dest))
    url = f"/uploads/files/{stored}"
    audit("image_upload", "project", puuid, safe_name)
    return jsonify({"ok": True, "url": url, "filename": safe_name})

# Statik uploads xizmat qilish
@app.route("/uploads/files/<filename>")
def serve_upload(filename):
    return send_from_directory(str(FILES_PATH), filename)



# ── Uptime Monitoring ──────────────────────────────────────────────────────
_uptime_data = {"checks": [], "last_down": None}

def _uptime_checker():
    """Har 60 sekundda serverni tekshiradi."""
    while True:
        time.sleep(60)
        try:
            t0 = time.time()
            import urllib.request as ur
            port = CFG["PORT"]
            try:
                ur.urlopen(f"http://127.0.0.1:{port}/login", timeout=5)
                status = "up"
            except Exception:
                status = "down"
            ms = int((time.time() - t0) * 1000)
            db_exec("INSERT INTO uptime_logs (status,response_ms) VALUES (?,?)", (status, ms), fetch=False)
            # Eski loglarni tozalash (7 kundan oshgan)
            db_exec("DELETE FROM uptime_logs WHERE checked_at < datetime('now','-7 days')", fetch=False)
        except Exception:
            pass

@app.route("/admin/uptime")
@admin_req
def admin_uptime():
    logs = db_exec("SELECT * FROM uptime_logs ORDER BY id DESC LIMIT 1440") or []  # 24 soat * 60
    total = len(logs)
    up_count = sum(1 for l in logs if l["status"] == "up")
    uptime_pct = round((up_count / total * 100), 2) if total else 100.0
    avg_ms = round(sum(l["response_ms"] or 0 for l in logs) / total, 1) if total else 0
    last_down = None
    for l in logs:
        if l["status"] == "down":
            last_down = str(l["checked_at"])[:19]
            break
    recent = logs[:60]  # Oxirgi 1 soat
    bars = "".join(f'<div style="width:2px;height:{min(30, max(3,(l["response_ms"] or 0)//10))}px;background:{"var(--gr)" if l["status"]=="up" else "var(--rd)"};border-radius:1px"></div>' for l in reversed(recent))
    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">📉 Uptime Monitoring</h2>
    <div class="g g4 mb">
      <div class="stat"><div class="v" style="color:{'var(--gr)' if uptime_pct > 99 else 'var(--yl)'}">{uptime_pct}%</div><div class="l">Uptime (7 kun)</div></div>
      <div class="stat"><div class="v">{avg_ms}</div><div class="l">O'rtacha javob (ms)</div></div>
      <div class="stat"><div class="v">{total}</div><div class="l">Tekshiruvlar soni</div></div>
      <div class="stat"><div class="v" style="font-size:1rem">{last_down or 'Hech qachon'}</div><div class="l">Oxirgi nosozlik</div></div>
    </div>
    <div class="card"><h3>Oxirgi 1 soat (har 1 daqiqa)</h3>
      <div style="display:flex;gap:1px;align-items:end;min-height:34px;padding:8px 0">{bars or '<span class="tm">Malumot yoq</span>'}</div>
    </div>"""
    return _pg("Uptime", body, "uptime")



# ── Audit Trail sahifasi (admin) ───────────────────────────────────────────
@app.route("/admin/audit")
@admin_req
def admin_audit():
    logs = db_exec("SELECT * FROM audit_log ORDER BY id DESC LIMIT 200") or []
    rows = "".join(f"""<tr>
      <td>{l.get('username') or '—'}</td>
      <td><span class="bx xb">{l['action']}</span></td>
      <td>{l.get('target_type') or '—'}</td>
      <td style="max-width:180px;overflow:hidden;text-overflow:ellipsis;font-size:.74rem">{(l.get('details') or '—')[:60]}</td>
      <td><code style="font-size:.72rem">{l.get('ip_address') or '—'}</code></td>
      <td class="tm" style="font-size:.73rem">{str(l['created_at'])[:19]}</td>
    </tr>""" for l in logs)
    body = f"""
    <h2 style="color:#fff;margin-bottom:14px">📝 Audit Trail</h2>
    <p class="tm mb" style="font-size:.79rem">Barcha muhim harakatlar logi. Kim, qachon, nima qilgani shu yerda ko'rinadi.</p>
    <div class="card" style="padding:0"><div class="tw">
      <table><thead><tr><th>Foydalanuvchi</th><th>Harakat</th><th>Turi</th><th>Tafsilotlar</th><th>IP</th><th>Vaqt</th></tr></thead>
      <tbody>{rows or '<tr><td colspan=6 style="text-align:center;color:var(--mt);padding:16px">Hali yozuv yoq</td></tr>'}</tbody></table>
    </div></div>"""
    return _pg("Audit Trail", body, "audit")



# ── README Generator ───────────────────────────────────────────────────────
@app.route("/api/readme/generate/<puuid>", methods=["POST"])
@user_req
@write_req
def readme_generate(puuid):
    proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        return jsonify({"ok": False}), 404
    files = db_exec("SELECT path,is_folder FROM project_files WHERE project_id=? ORDER BY path", (proj["id"],)) or []
    tree_lines = []
    for f in files:
        depth = f["path"].count("/")
        prefix = "  " * depth + ("📁 " if f["is_folder"] else "📄 ")
        tree_lines.append(prefix + f["path"].split("/")[-1])
    tree = "\n".join(tree_lines) or "Fayl yo'q"
    readme = f"""# {proj['name']}

## Loyiha haqida
Bu loyiha SrvManager platformasida yaratilgan.

## Fayl tuzilmasi
```
{tree}
```

## Ishga tushirish
1. Fayllarni yuklab oling (ZIP)
2. `index.html` ni brauzerda oching

## Texnologiyalar
- HTML5
- CSS3
- JavaScript

## Muallif
Yaratilgan: {str(proj.get('created_at',''))[:10]}

---
*SrvManager tomonidan avtomatik yaratilgan*
"""
    db_exec("INSERT INTO project_files (project_id,path,is_folder,content) VALUES (?,?,0,?) "
            "ON CONFLICT(project_id,path) DO UPDATE SET content=excluded.content,updated_at=datetime('now')",
            (proj["id"], "README.md", readme), fetch=False)
    audit("readme_generate", "project", puuid)
    return jsonify({"ok": True, "content": readme})



# ── Markdown Editor (preview API) ──────────────────────────────────────────
@app.route("/api/markdown/preview", methods=["POST"])
@user_req
def markdown_preview():
    """Oddiy Markdown ni HTML ga aylantiradi (server tomonda)."""
    d = request.get_json() or {}
    md_text = d.get("text", "")
    # Oddiy markdown parser (tashqi kutubxonasiz)
    html_out = _simple_md_to_html(md_text)
    return jsonify({"html": html_out})

def _simple_md_to_html(text):
    """Minimal markdown -> HTML konverter."""
    import re as _re
    lines = text.split("\n")
    html_lines = []
    in_code = False
    for line in lines:
        if line.startswith("```"):
            if in_code:
                html_lines.append("</pre></code>")
                in_code = False
            else:
                html_lines.append("<code><pre>")
                in_code = True
            continue
        if in_code:
            html_lines.append(line)
            continue
        # Headings
        if line.startswith("### "):
            html_lines.append(f"<h3>{line[4:]}</h3>")
        elif line.startswith("## "):
            html_lines.append(f"<h2>{line[3:]}</h2>")
        elif line.startswith("# "):
            html_lines.append(f"<h1>{line[2:]}</h1>")
        elif line.startswith("- ") or line.startswith("* "):
            html_lines.append(f"<li>{line[2:]}</li>")
        elif line.startswith("> "):
            html_lines.append(f"<blockquote>{line[2:]}</blockquote>")
        elif line.strip() == "---":
            html_lines.append("<hr>")
        elif line.strip() == "":
            html_lines.append("<br>")
        else:
            # Inline formatting
            l = line
            l = _re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', l)
            l = _re.sub(r'\*(.+?)\*', r'<em>\1</em>', l)
            l = _re.sub(r'`(.+?)`', r'<code>\1</code>', l)
            l = _re.sub(r'\[(.+?)\]\((.+?)\)', r'<a href="\2">\1</a>', l)
            l = _re.sub(r'!\[(.+?)\]\((.+?)\)', r'<img src="\2" alt="\1">', l)
            html_lines.append(f"<p>{l}</p>")
    if in_code:
        html_lines.append("</pre></code>")
    return "\n".join(html_lines)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║         OFFLINE AI YORDAMCHI — mahalliy fayllar asosida ishlaydi         ║
# ╚══════════════════════════════════════════════════════════════════════════╝
AI_DATA_DIR = Path("ai_data")
AI_DATA_DIR.mkdir(exist_ok=True)
AI_KNOWLEDGE_FILE = AI_DATA_DIR / "knowledge.json"
AI_TOPICS_FILE = AI_DATA_DIR / "topics.json"
AI_WORDS_FILE = AI_DATA_DIR / "question_words.json"
AI_BADWORDS_FILE = AI_DATA_DIR / "badwords.json"

# ── Haqoratli so'zlar filtri ──────────────────────────────────────────────
# Foydalanuvchi o'zi qo'shadi — standart ro'yxat BO'SH
_DEFAULT_BADWORDS = []

def _load_badwords():
    if AI_BADWORDS_FILE.exists():
        try:
            with open(AI_BADWORDS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                return data.get("words", []) if isinstance(data, dict) else data
        except Exception:
            pass
    return _DEFAULT_BADWORDS

def _load_badword_responses():
    """Haqoratli so'zga javob matnini yuklaydi."""
    if AI_BADWORDS_FILE.exists():
        try:
            with open(AI_BADWORDS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, dict):
                    return data.get("response", "")
        except Exception:
            pass
    return ""

def _save_badwords_data(words, response=""):
    with open(AI_BADWORDS_FILE, "w", encoding="utf-8") as f:
        json.dump({"words": words, "response": response}, f, ensure_ascii=False, indent=2)

def _contains_profanity(text):
    """Matnda haqoratli so'z bor-yo'qligini tekshiradi."""
    badwords = _load_badwords()
    if not badwords:
        return False
    cleaned = re.sub(r'[^a-zA-Z0-9\u0400-\u04FF]', '', text.lower())
    text_lower = text.lower()
    for word in badwords:
        if not word or len(word) < 2:
            continue
        word_clean = re.sub(r'[^a-zA-Z0-9\u0400-\u04FF]', '', word.lower())
        if len(word_clean) < 2:
            continue
        if word_clean in cleaned:
            return True
        if word.lower() in text_lower:
            return True
        # Harflar orasiga belgi qo'yilgan holat
        if len(word) >= 3:
            pattern = r'[^a-zA-Z\u0400-\u04FF]*'.join(re.escape(ch) for ch in word.lower())
            if re.search(pattern, text_lower):
                return True
    return False

# ── Bilim bazasi yuklash/saqlash ──────────────────────────────────────────
def _load_ai_knowledge():
    if not AI_KNOWLEDGE_FILE.exists():
        return []
    try:
        with open(AI_KNOWLEDGE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def _save_ai_knowledge(data):
    with open(AI_KNOWLEDGE_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

# ── Mavzular (topic + info) ──────────────────────────────────────────────
def _load_ai_topics():
    if not AI_TOPICS_FILE.exists():
        return []
    try:
        with open(AI_TOPICS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def _save_ai_topics(data):
    with open(AI_TOPICS_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

# ── Savol so'zlari (nima, qanday, ...) ───────────────────────────────────
def _load_question_words():
    if not AI_WORDS_FILE.exists():
        defaults = ["nima", "qanday", "necha", "qachon", "kim", "qayerda", "nega", "qancha"]
        _save_question_words(defaults)
        return defaults
    try:
        with open(AI_WORDS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return ["nima", "qanday"]

def _save_question_words(words):
    with open(AI_WORDS_FILE, "w", encoding="utf-8") as f:
        json.dump(words, f, ensure_ascii=False, indent=2)

# ── HTML/CSS/Emmet bilim bazasi ────────────────────────────────────────────
_HTML_TAGS = {
    "div": ("Block konteyner element", "<div>Mazmun</div>", "Elementlarni guruhlash, layout yaratish uchun ishlatiladi"),
    "span": ("Inline konteyner", "<span>matn</span>", "Matn ichida kichik qismni ajratish uchun"),
    "p": ("Paragraf (abzats)", "<p>Matn</p>", "Matn paragraflarini yaratish uchun"),
    "a": ("Havola (link)", '<a href="url">Matn</a>', "Boshqa sahifaga yoki manzilga havola yaratadi"),
    "img": ("Rasm", '<img src="rasm.jpg" alt="tavsif">', "Sahifaga rasm qo'shadi. Yopiluvchi teg yo'q"),
    "h1": ("1-darajali sarlavha", "<h1>Sarlavha</h1>", "Eng katta sarlavha. h1-h6 gacha bor"),
    "h2": ("2-darajali sarlavha", "<h2>Sarlavha</h2>", "Ikkinchi darajali sarlavha"),
    "h3": ("3-darajali sarlavha", "<h3>Sarlavha</h3>", "Uchinchi darajali sarlavha"),
    "ul": ("Tartibsiz ro'yxat", "<ul><li>Element</li></ul>", "Nuqtali ro'yxat yaratadi"),
    "ol": ("Tartibli ro'yxat", "<ol><li>Element</li></ol>", "Raqamli ro'yxat yaratadi"),
    "li": ("Ro'yxat elementi", "<li>Element</li>", "ul yoki ol ichida ishlatiladi"),
    "table": ("Jadval", "<table><tr><td>Katak</td></tr></table>", "Ma'lumotlarni jadval ko'rinishida ko'rsatadi"),
    "tr": ("Jadval qatori", "<tr>...</tr>", "table ichida qator yaratadi"),
    "td": ("Jadval katagi", "<td>Ma'lumot</td>", "tr ichida katak yaratadi"),
    "th": ("Jadval sarlavha katagi", "<th>Sarlavha</th>", "Qalin va markazlashtirilgan katak"),
    "form": ("Forma", '<form action="/url" method="POST">...</form>', "Foydalanuvchi kiritgan ma'lumotlarni yuborish uchun"),
    "input": ("Kiritish maydoni", '<input type="text" name="ism">', "Matn, parol, checkbox va boshqa turlar"),
    "button": ("Tugma", "<button>Bosish</button>", "Bosiladigan tugma yaratadi"),
    "textarea": ("Ko'p qatorli matn", "<textarea>Matn</textarea>", "Katta matn kiritish maydoni"),
    "select": ("Tanlash ro'yxati", "<select><option>1</option></select>", "Dropdown ro'yxat yaratadi"),
    "nav": ("Navigatsiya", "<nav>Havolalar</nav>", "Sayt navigatsiyasi uchun semantik teg"),
    "header": ("Sarlavha bo'limi", "<header>...</header>", "Sahifa yoki bo'lim sarlavhasi"),
    "footer": ("Pastki bo'lim", "<footer>...</footer>", "Sahifa pastki qismi (muallif, havolalar)"),
    "section": ("Bo'lim", "<section>...</section>", "Sahifani mantiqiy bo'limlarga ajratish"),
    "article": ("Maqola", "<article>...</article>", "Mustaqil mazmunli bo'lim (blog post, yangilik)"),
    "aside": ("Yon panel", "<aside>...</aside>", "Asosiy mazmun bilan bog'liq qo'shimcha ma'lumot"),
    "main": ("Asosiy mazmun", "<main>...</main>", "Sahifaning asosiy mazmuni (bitta bo'lishi kerak)"),
    "br": ("Qator uzish", "<br>", "Yangi qatorga o'tish. Yopiluvchi teg yo'q"),
    "hr": ("Gorizontal chiziq", "<hr>", "Ajratuvchi gorizontal chiziq"),
    "strong": ("Qalin matn", "<strong>Muhim</strong>", "Qalin va semantik jihatdan muhim matn"),
    "em": ("Kursiv matn", "<em>Ta'kidlangan</em>", "Kursiv va ta'kidlangan matn"),
    "code": ("Kod", "<code>let x = 5;</code>", "Dasturlash kodini ko'rsatish uchun"),
    "pre": ("Formatlangan matn", "<pre>  bo'sh joy  </pre>", "Bo'sh joylar va qatorlar saqlanadi"),
    "link": ("Tashqi resurs", '<link rel="stylesheet" href="style.css">', "CSS fayl ulash uchun head ichida"),
    "script": ("JavaScript", '<script src="app.js"></script>', "JS kodni ulash yoki yozish uchun"),
    "meta": ("Meta ma'lumot", '<meta charset="UTF-8">', "Sahifa haqida meta ma'lumot (head ichida)"),
    "title": ("Sahifa nomi", "<title>Nomi</title>", "Brauzer tabida ko'rinadigan nom"),
    "style": ("Ichki CSS", "<style>body{color:red}</style>", "HTML ichida CSS yozish uchun"),
    "video": ("Video", '<video src="video.mp4" controls></video>', "Video o'ynatish uchun"),
    "audio": ("Audio", '<audio src="audio.mp3" controls></audio>', "Musiqa/ovoz o'ynatish uchun"),
    "iframe": ("Ichki ramka", '<iframe src="url"></iframe>', "Boshqa sahifani ichiga joylashtirish"),
    "canvas": ("Grafik", '<canvas id="c"></canvas>', "JavaScript bilan rasm chizish uchun"),
    "label": ("Yorliq", '<label for="id">Matn</label>', "input uchun nom/yorliq"),
}

_CSS_PROPS = {
    "display": "Elementning ko'rinish turi: block, inline, flex, grid, none",
    "flexbox": "display:flex; — elementlarni bir qatorda yoki ustunda joylashtirish. align-items, justify-content bilan boshqariladi",
    "grid": "display:grid; — 2D tarmoq (setka) yaratish. grid-template-columns, grid-gap bilan boshqariladi",
    "margin": "Tashqi bo'shliq. margin: 10px; yoki margin-top, margin-bottom, margin-left, margin-right",
    "padding": "Ichki bo'shliq. padding: 10px; yoki padding-top, padding-bottom...",
    "border": "Chegara. border: 1px solid #000; — qalinlik, tur, rang",
    "border-radius": "Burchakni yumaloqlash. border-radius: 10px; yoki 50% (doira)",
    "color": "Matn rangi. color: red; yoki color: #ff0000; yoki color: rgb(255,0,0);",
    "background": "Fon. background: #fff; yoki background-image, background-color",
    "font-size": "Matn o'lchami. font-size: 16px; yoki 1.2rem, 1.5em",
    "font-weight": "Matn qalinligi. font-weight: bold; yoki 100-900 (400=normal, 700=bold)",
    "text-align": "Matn joylashuvi. text-align: center/left/right/justify",
    "position": "Joylashuv turi: static, relative, absolute, fixed, sticky",
    "z-index": "Qatlam tartibi. Katta son = ustda ko'rinadi. position: relative/absolute bo'lishi kerak",
    "width": "Kenglik. width: 100%; yoki 300px, 50vw",
    "height": "Balandlik. height: 100vh; (viewport height), 200px",
    "overflow": "Toshib ketgan mazmun. overflow: hidden/scroll/auto",
    "opacity": "Shaffoflik. opacity: 0 (ko'rinmas) dan 1 (to'liq) gacha",
    "transition": "Animatsiya. transition: all 0.3s ease; — o'zgarishlarni silliq qiladi",
    "transform": "O'zgartirish. transform: rotate(45deg), scale(1.5), translate(10px,20px)",
    "box-shadow": "Soya. box-shadow: 0 4px 12px rgba(0,0,0,0.2);",
    "cursor": "Sichqoncha ko'rinishi. cursor: pointer (qo'l), default, text, move",
}

_EMMET_EXAMPLES = {
    "div*10": "10 ta <div></div> yaratadi",
    "div*5": "5 ta <div></div> yaratadi",
    "ul>li*5": "<ul> ichida 5 ta <li></li> yaratadi",
    "ul>li*3": "<ul> ichida 3 ta <li></li> yaratadi",
    "nav>ul>li*4>a": "Navigatsiya: nav > ul > 4 ta li > har birida a tegi",
    "div.box": '<div class="box"></div> yaratadi',
    "div#main": '<div id="main"></div> yaratadi',
    "div.box#main": '<div class="box" id="main"></div>',
    "div.item$*3": '<div class="item1"></div>\n<div class="item2"></div>\n<div class="item3"></div>',
    "h1+p+p": "<h1></h1>\n<p></p>\n<p></p> — bir xil darajada",
    "div>p>span": "Ichma-ich: div > p > span",
    "(div>p)*3": "Guruhni 3 marta: div>p, div>p, div>p",
    "a[href=#]": '<a href="#"></a>',
    'a{Havola}': '<a href="">Havola</a> — {} ichida matn',
    "!": "HTML5 to'liq shablon (doctype, html, head, body)",
    "img": '<img src="" alt=""> yaratadi (avtomatik atributlar)',
    "input": '<input type="text"> yaratadi',
    "link": '<link rel="stylesheet" href=""> yaratadi',
    "div+p": "<div></div>\n<p></p> — qo'shni elementlar",
    "div>p+span": "<div>\n  <p></p>\n  <span></span>\n</div>",
    "table>tr*3>td*4": "3 qatorli, 4 ustunli jadval",
    "form>input*3+button": "Forma: 3 ta input va 1 tugma",
    "lorem": "30 so'zlik lorem ipsum matn",
    "lorem10": "10 so'zlik lorem ipsum matn",
    "div.container>header+main+footer": "Oddiy sahifa tuzilmasi",
}

def _ai_emmet_answer(q_lower, name):
    """Emmet haqidagi savollarga javob."""
    # Umumiy Emmet haqida
    if re.search(r'emmet\s*(nima|nim|haqida|degan|bu)', q_lower) or q_lower.strip() == "emmet":
        return f"✨ **Emmet** — HTML va CSS yozishni tezlashtiradigan qisqartmalar tizimi, {name}.\n\nMasalan:\n• `div.box` → `<div class=\"box\"></div>`\n• `ul>li*5` → ul ichida 5 ta li\n• `!` → to'liq HTML5 shablon\n• `div*10` → 10 ta div\n\n📝 Qisqartmani yozib **Tab** bosing — avtomatik kengayadi!\n\nBatafsil so'rang: \"div*10 nima qiladi\" yoki \"ul>li*3 kengaytmasi\""

    # Aniq Emmet misol so'ralsa
    for pattern, explanation in _EMMET_EXAMPLES.items():
        # "div*10 nima" yoki "div*10 kengaytmasi" yoki shunchaki "div*10"
        pat_escaped = re.escape(pattern).replace(r'\*', r'\*').replace(r'\$', r'\$')
        if re.search(pat_escaped, q_lower):
            return f"✨ **Emmet: `{pattern}`**\n\nNatija: {explanation}\n\nMuharrirda yozib **Tab** bosing!"

    # Umumiy emmet patternni tushuntirish
    emmet_q = re.search(r'([\w.#>\+\*\[\]\{\}\(\)\$\!]+)\s*(nima|nim|qiladi|kengayt|natija|yoz)', q_lower)
    if emmet_q:
        abbr = emmet_q.group(1)
        # Oddiy Emmet qoidalarini tushuntirish
        parts = []
        if '*' in abbr:
            parts.append(f"• `*N` — elementni N marta takrorlaydi")
        if '>' in abbr:
            parts.append(f"• `>` — ichma-ich (child) element yaratadi")
        if '+' in abbr:
            parts.append(f"• `+` — qo'shni (sibling) element yaratadi")
        if '.' in abbr:
            parts.append(f"• `.nom` — class atributi qo'shadi")
        if '#' in abbr:
            parts.append(f"• `#nom` — id atributi qo'shadi")
        if '$' in abbr:
            parts.append(f"• `$` — raqam qo'shadi (1, 2, 3...)")
        if '(' in abbr:
            parts.append(f"• `()` — guruh yaratadi")
        if '[' in abbr:
            parts.append(f"• `[attr=val]` — atribut qo'shadi")
        if '{' in abbr:
            parts.append(f"• `{{matn}}` — element ichiga matn qo'shadi")
        if parts:
            explanation = "\n".join(parts)
            return f"✨ **Emmet: `{abbr}`**\n\nQoidalar:\n{explanation}\n\n📝 Muharrirda yozib **Tab** bosing!"

    return None

def _ai_html_answer(q_lower, name):
    """HTML teglar haqidagi savollarga javob."""
    # "div nima", "img tegi", "table qanday" kabi
    for tag, (desc, example, detail) in _HTML_TAGS.items():
        patterns = [
            rf'\b{tag}\b\s*(nima|nim|teg|haqida|qanday|degan|vazifa|ishlatil)',
            rf'(nima|nim|qanday)\s*(bu\s*)?\b{tag}\b',
            rf'\b{tag}\b\s*teg',
        ]
        for pat in patterns:
            if re.search(pat, q_lower):
                return f"🌐 **`<{tag}>` — {desc}**\n\nMisol: `{example}`\n\n📖 {detail}"

    # Umumiy HTML haqida
    if re.search(r'html\s*(nima|nim|haqida|degan|bu|o.?rgan|ayt)', q_lower):
        return f"🌐 **HTML** (HyperText Markup Language) — veb-sahifalar yaratish tili, {name}.\n\nAsosiy teglar:\n• `<div>` — block konteyner\n• `<p>` — paragraf\n• `<a>` — havola\n• `<img>` — rasm\n• `<h1>`-`<h6>` — sarlavhalar\n• `<ul>/<ol>` — ro'yxatlar\n• `<table>` — jadval\n• `<form>` — forma\n\nAniq teg haqida so'rang: \"div nima\" yoki \"img tegi\""

    return None

def _ai_css_answer(q_lower, name):
    """CSS haqidagi savollarga javob."""
    for prop, desc in _CSS_PROPS.items():
        patterns = [
            rf'\b{re.escape(prop)}\b\s*(nima|nim|haqida|qanday|degan|ishlatil|qiladi)',
            rf'(nima|nim|qanday)\s*(bu\s*)?\b{re.escape(prop)}\b',
        ]
        for pat in patterns:
            if re.search(pat, q_lower):
                return f"🎨 **CSS: `{prop}`**\n\n{desc}"

    # Umumiy CSS haqida
    if re.search(r'css\s*(nima|nim|haqida|degan|bu|o.?rgan|ayt)', q_lower):
        return f"🎨 **CSS** (Cascading Style Sheets) — HTML elementlarning ko'rinishini boshqaradi, {name}.\n\nAsosiy xususiyatlar:\n• `display` — ko'rinish turi (flex, grid, block)\n• `margin/padding` — tashqi/ichki bo'shliq\n• `color` — matn rangi\n• `background` — fon\n• `border` — chegara\n• `position` — joylashuv\n• `font-size` — matn o'lchami\n\nAniq xususiyat haqida so'rang: \"flexbox nima\" yoki \"margin padding\""

    return None

def _ai_solve_math(text):
    """Matematik ifodani hisoblashga urinadi. Xavfsiz eval."""
    # Matndan raqam va operatorlarni ajratib olish
    # "2+2 javobi nechchi" -> "2+2", "2+2 nechchi" -> "2+2"
    cleaned = re.sub(r'(javobi|javob|nechchi|necha|nechta|qancha|hisobla|hisob)', '', text.lower()).strip()
    cleaned = re.sub(r'[^\d+\-*/().%^ ]', '', cleaned).strip()
    if not cleaned or not re.search(r'\d', cleaned):
        return None
    # ^ ni ** ga aylantirish
    cleaned = cleaned.replace('^', '**')
    try:
        # Faqat xavfsiz belgilar
        if re.match(r'^[\d+\-*/().%\s*]+$', cleaned):
            result = eval(cleaned, {"__builtins__": {}}, {})
            if isinstance(result, float) and result == int(result):
                result = int(result)
            return str(result)
    except Exception:
        pass
    return None

def _ai_play_game(text):
    """Oddiy o'yinlar va amaliy vositalar."""
    import random
    t = text.lower().strip()

    # ── Lorem generatori ──
    lorem_match = re.search(r'lorem\s*(\d+)?', t)
    if lorem_match and ("lorem" in t):
        n = int(lorem_match.group(1) or 30)
        words = ('lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod tempor '
                 'incididunt ut labore et dolore magna aliqua ut enim ad minim veniam quis nostrud '
                 'exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat duis aute '
                 'irure dolor in reprehenderit voluptate velit esse cillum dolore eu fugiat nulla '
                 'pariatur excepteur sint occaecat cupidatat non proident sunt culpa qui officia '
                 'deserunt mollit anim id est laborum').split()
        result = ' '.join(words[i % len(words)] for i in range(n))
        result = result[0].upper() + result[1:] + '.'
        return f"📐 **Lorem ({n} so'z):**\n\n{result}"

    # ── Son topish o'yini ──
    if re.search(r'son\s*top|topishmoq.*son|son.*o.?yin', t):
        n = random.randint(1, 100)
        # Saqlaymiz session ga (keyingi xabarlarda tekshirish uchun)
        hints = []
        if n < 50: hints.append("50 dan kichik")
        else: hints.append("50 dan katta")
        if n % 2 == 0: hints.append("juft son")
        else: hints.append("toq son")
        return f"🎯 **Son topish o'yini!**\n\nMen 1 dan 100 gacha son o'yladim.\n\n💡 Maslahat: {hints[0]}, {hints[1]}.\n\nJavobingizni yozing! (To'g'ri javob: ||{n}||)"

    # ── Eslatma / Timer ──
    reminder_match = re.search(r'(\d+)\s*(daqiqa|minut|min|sekund|sek|sec|soat)', t)
    if reminder_match and any(w in t for w in ["eslat", "timer", "vaqt", "bildir", "ogohlantir"]):
        amount = int(reminder_match.group(1))
        unit = reminder_match.group(2)
        if "sek" in unit or "sec" in unit:
            ms = amount * 1000
            unit_name = "sekund"
        elif "soat" in unit:
            ms = amount * 3600000
            unit_name = "soat"
        else:
            ms = amount * 60000
            unit_name = "daqiqa"
        return f"⏰ **Eslatma qo'yildi!**\n\n{amount} {unit_name} dan keyin bildirishnoma keladi.\n\n||TIMER:{ms}||"

    # ── Vaqt/sana ──
    if any(w in t for w in ["soat", "vaqt", "nechanchi", "bugun", "sana", "kun"]):
        if any(w in t for w in ["soat", "vaqt", "nech"]):
            now = datetime.now()
            return f"🕐 Hozir: **{now.strftime('%H:%M:%S')}**\n📅 Sana: **{now.strftime('%Y-%m-%d')}** ({['Dushanba','Seshanba','Chorshanba','Payshanba','Juma','Shanba','Yakshanba'][now.weekday()]})"
        if any(w in t for w in ["bugun", "sana", "nechanchi", "kun"]):
            now = datetime.now()
            kunlar = ['Dushanba','Seshanba','Chorshanba','Payshanba','Juma','Shanba','Yakshanba']
            oylar = ['Yanvar','Fevral','Mart','Aprel','May','Iyun','Iyul','Avgust','Sentyabr','Oktyabr','Noyabr','Dekabr']
            return f"📅 Bugun: **{now.day}-{oylar[now.month-1]}, {now.year}-yil** ({kunlar[now.weekday()]})"

    # ── Tosh-qaychi-qog'oz ──
    if any(w in t for w in ["tosh", "qaychi", "qogoz", "qog'oz", "kagoz"]):
        choices = ["tosh", "qaychi", "qogoz"]
        user_choice = None
        if "tosh" in t: user_choice = "tosh"
        elif "qaychi" in t: user_choice = "qaychi"
        elif any(w in t for w in ["qogoz", "qog'oz", "kagoz"]): user_choice = "qogoz"
        if user_choice:
            ai_choice = random.choice(choices)
            wins = {"tosh": "qaychi", "qaychi": "qogoz", "qogoz": "tosh"}
            emoji = {"tosh": "🪨", "qaychi": "✂️", "qogoz": "📄"}
            if user_choice == ai_choice:
                return f"Men: {emoji[ai_choice]} {ai_choice}\nSiz: {emoji[user_choice]} {user_choice}\n\n🤝 Durrang!"
            elif wins[user_choice] == ai_choice:
                return f"Men: {emoji[ai_choice]} {ai_choice}\nSiz: {emoji[user_choice]} {user_choice}\n\n🎉 Siz yutdingiz!"
            else:
                return f"Men: {emoji[ai_choice]} {ai_choice}\nSiz: {emoji[user_choice]} {user_choice}\n\n😎 Men yutdim!"
        return "Tosh-qaychi-qogoz: 'tosh', 'qaychi' yoki 'qogoz' yozing!"

    # ── O'yinlar ro'yxati ──
    if any(w in t for w in ["oyin", "o'yin", "oyna", "game", "zerik"]):
        return "🎮 **O'yinlar va vositalar:**\n\n• 🪨 Tosh-qaychi-qogoz: 'tosh', 'qaychi', 'qogoz'\n• 🎯 Son topish: 'son top'\n• 🧮 Matematik: '2+2', '15*3', '(5+3)*2'\n• 🎲 Tasodifiy son: 'son ber'\n• 😂 Latifa: 'latifa'\n• 📐 Lorem: 'lorem 50'\n• 🕐 Vaqt: 'soat nechchi', 'bugun'\n• ⏰ Eslatma: '5 daqiqadan keyin eslatib tur'"

    # ── Tasodifiy son ──
    if "son" in t and ("ber" in t or "ayt" in t):
        n = random.randint(1, 100)
        return f"🎲 Tasodifiy son: **{n}**"

    # ── Latifa ──
    if any(w in t for w in ["latifa", "hazil", "kul", "anekdot"]):
        jokes = [
            "Dasturchi nega yomg'irni yaxshi ko'radi? Chunki bug (xato) lar yo'qoladi! 😄",
            "— Salom, texnik yordam? Kompyuterim ishlamayapti.\n— Yoqib ko'rdingizmi?\n— Ha, juda yoqadi! 😂",
            "Dasturchi turmushga chiqdi... catch blokida 💍",
            "Wi-Fi parolni bilasizmi?\n— Ha, devorga yozilgan.\n— 12345678mi?\n— Yo'q, 'devorga_yozilgan' 😂",
            "Nechta dasturchi lampochka almashtirishi kerak? Hech biri — bu hardware muammo! 💡",
            "404: Latifa topilmadi... 😜 Hazil, mana:\nHTML ni CSS siz ko'rganmisiz? Yalang'och! 🙈",
        ]
        return random.choice(jokes)

    return None

# ── Loyiha yordamchisi ────────────────────────────────────────────────────
def _ai_project_helper(q_lower, name):
    """Loyiha fayllari haqida ma'lumot beradi."""
    if not any(w in q_lower for w in ["loyiha", "fayl", "project", "papka", "index", "nechta"]):
        return None
    # Foydalanuvchining loyihalari
    uid = session.get("user_id", 0)
    if any(w in q_lower for w in ["nechta fayl", "fayl soni", "fayllar"]):
        projs = db_exec("SELECT p.name,p.uuid,(SELECT COUNT(*) FROM project_files WHERE project_id=p.id) as cnt FROM projects p WHERE p.owner_id=? ORDER BY p.updated_at DESC LIMIT 5", (uid,)) or []
        if not projs:
            return f"{name}, sizda hali loyiha yo'q. /projects sahifasidan yangi loyiha yarating!"
        lines = "\n".join([f"• **{p['name']}** — {p['cnt']} ta fayl" for p in projs])
        return f"📁 **Sizning loyihalaringiz:**\n\n{lines}"
    if any(w in q_lower for w in ["loyiha", "project", "nechta loyiha"]):
        cnt = q1("SELECT COUNT(*) c FROM projects WHERE owner_id=?", (uid,))
        total = cnt["c"] if cnt else 0
        return f"📁 {name}, sizda jami **{total}** ta loyiha bor.\n\n'nechta fayl' deb so'rang — har bir loyihadagi fayllar sonini ko'rsataman."
    return None

def _ai_find_answer(question, username="", history=None):
    """Savol uchun eng yaxshi javobni topadi."""
    q_lower = question.lower().strip()
    q_words = set(re.findall(r'\w+', q_lower))
    question_words = _load_question_words()
    name = username or "foydalanuvchi"
    hist = history or []

    # ── Oldingi suhbatga murojat ──
    memory_patterns = [r"oldin\s*(nima|nim)", r"avval\s*(nima|nim)", r"esla",
                       r"birinchi\s*savol", r"oxirgi\s*savol", r"nima\s*degan\s*edim",
                       r"nima\s*so.?ragan", r"tarix"]
    for pat in memory_patterns:
        if re.search(pat, q_lower):
            if not hist:
                return f"Hali suhbatimiz boshlanmagan, {name}. Menga biror narsa so'rang! 😊"
            last_msgs = hist[-5:]
            memory_text = "\n".join([f"• Siz: {m['q']}\n  Men: {m['a'][:80]}..." for m in last_msgs])
            return f"📝 So'nggi suhbatimiz, {name}:\n\n{memory_text}\n\n(Jami {len(hist)} ta xabar saqlangan)"

    # ── Matematik amallar ──
    math_result = _ai_solve_math(question)
    if math_result is not None:
        return f"🧮 Javob: **{math_result}**"

    # ── O'yinlar ──
    game_result = _ai_play_game(question)
    if game_result is not None:
        return game_result

    # ── Loyiha yordamchisi ──
    proj_result = _ai_project_helper(q_lower, name)
    if proj_result:
        return proj_result

    # ── AI o'zi haqida ──
    ai_about_patterns = [
        r"sen\s*kim", r"siz\s*kim", r"kim\s*sen", r"kimsan",
        r"o.?zi.?\s*haqida", r"o.?zing\s*haqida",
        r"sen\s*nima", r"siz\s*nima.?siz",
        r"qanday\s*(?:dastur|bot|ai|sun.?iy)",
    ]
    for pat in ai_about_patterns:
        if re.search(pat, q_lower):
            return f"Men — AI Yordamchi, mahalliy (offline) sun'iy intellekt bo'tman. 🤖\n\nMening xususiyatlarim:\n• Internetga ulanmasdan ishlayman\n• Bilim bazam ai_data/ papkasida saqlanadi\n• Matematik misollarni yechaman\n• O'yin o'ynay olaman\n• Siz o'rgatgan narsalarni eslab qolaman\n• {name}, siz menga yangi bilim qo'shishingiz mumkin!\n\nMen SrvManager platformasi uchun yaratilganman."

    # ── Ism haqida savollar ──
    name_patterns = [
        r"ism(?:ing|im|i)?\s*(?:nima|nim|ni|kim)",
        r"(?:nima|nim|ni|kim)\s*(?:sen|siz|sani|sizni)?\s*ism",
        r"seni?\s*(?:nima|nim)\s*deyishadi",
        r"(?:nima|nim)\s*(?:deb|dep)\s*(?:atashadi|chaqirishadi)",
        r"ism(?:ing)?\s*(?:bormi|ayt)",
        r"oting\s*nima", r"nima\s*oting",
    ]
    for pat in name_patterns:
        if re.search(pat, q_lower):
            return f"Mening ismim **AI Yordamchi**. Men SrvManager platformasining sun'iy intellekt yordamchisiman. {name}, sizga doimo yordam berishga tayyorman! 🤖"

    # ── Salomlashish (kengaytirilgan) ──
    greetings = {"salom", "assalom", "assalomu", "hey", "hi", "hello", "hayrli",
                 "xayrli", "salomlashish", "salom aleykum", "va aleykum",
                 "yahshimisiz", "yaxshimisiz", "qalay", "qalaysiz", "tinchmi"}
    if q_words & greetings:
        import random
        responses = [
            f"Salom, {name}! 👋 Bugun sizga qanday yordam bera olaman?",
            f"Assalomu alaykum, {name}! Men tayyorman — savolingizni bering!",
            f"Salom-salom, {name}! 😊 Nima qilaylik bugun?",
            f"Hey, {name}! Yaxshi kuningiz bo'lsin! Qanday yordam kerak?",
            f"Assalomu alaykum, {name}! Xizmatingizdaman. 🤖",
        ]
        return random.choice(responses)

    # ── Rahmat ──
    thanks = {"rahmat", "raxmat", "thanks", "thank", "tashakkur", "katta rahmat", "minnatdor"}
    if q_words & thanks:
        import random
        responses = [
            f"Arzimaydi, {name}! Har doim xizmatingizdaman. 😊",
            f"Marhamat, {name}! Yana savollaringiz bo'lsa — bemalol!",
            f"Sizga yordam bera olganimdan xursandman, {name}! 🌟",
        ]
        return random.choice(responses)

    # ── Xayrlashish ──
    byes = {"hayr", "xayr", "ko'rishguncha", "bye", "goodbye", "salomat"}
    if q_words & byes:
        return f"Xayr, {name}! Yaxshi kuningiz bo'lsin! Kerak bo'lganda qaytib keling. 👋😊"

    # ── Ahvol so'rash ──
    mood_q = {"qalay", "qalaysiz", "yaxshi", "ahvol", "kayfiyat"}
    if q_words & mood_q and len(q_words) <= 4:
        return f"Rahmat so'raganingiz uchun, {name}! Men — dasturman, har doim a'lo holatdaman! 😄 Sizchi, qanday yordam kerak?"

    # ── Nima qila olasan? ──
    ability_patterns = [r"nima\s*qila\s*olasan", r"imkoniyat", r"funksiya", r"qanday.*yordam",
                        r"nima\s*bilasan", r"nimalar.*mumkin"]
    for pat in ability_patterns:
        if re.search(pat, q_lower):
            return f"Men quyidagilarni qila olaman, {name}:\n\n🧮 Matematik misollar yechish (2+2, 100/4, 2^10)\n🎮 O'yin o'ynash (tosh-qaychi-qogoz, latifa, tasodifiy son)\n📚 Savollaringizga javob berish (o'rgatilgan bilimlar asosida)\n💬 Suhbatlashish va salomlashish\n🌐 HTML teglar, CSS kodlar, Emmet qisqartmalar haqida gapirish\n📝 Yangi bilim qabul qilish (O'qitish tugmasi)\n\nMenga savol bering yoki biror narsa o'rgating!"

    # ── Emmet qisqartmalari ──
    emmet_result = _ai_emmet_answer(q_lower, name)
    if emmet_result:
        return emmet_result

    # ── HTML teglar haqida ──
    html_result = _ai_html_answer(q_lower, name)
    if html_result:
        return html_result

    # ── CSS haqida ──
    css_result = _ai_css_answer(q_lower, name)
    if css_result:
        return css_result

    # ── Mavzu bo'yicha qidiruv: "(mavzu) nima" yoki "nima (mavzu)" ──
    topics = _load_ai_topics()
    for topic in topics:
        topic_name = topic.get("topic", "").lower()
        topic_words = set(re.findall(r'\w+', topic_name))
        # Mavzu so'zlari savolda bormi?
        if topic_words and topic_words.issubset(q_words):
            # Va savol so'zi ham bormi?
            has_qword = any(qw in q_words for qw in question_words)
            # Yoki to'g'ridan-to'g'ri moslik
            if has_qword or topic_name in q_lower:
                return topic["info"]

    # ── Oddiy bilim bazasi bo'yicha qidiruv ──
    knowledge = _load_ai_knowledge()
    if not knowledge and not topics:
        return f"Salom, {name}! Men yangi AI yordamchiman. 🤖 Hozircha bilim bazam bo'sh, lekin siz menga o'rgatishingiz mumkin!\n\n📚 O'qitish tugmasini bosing va savol-javob qo'shing.\n\nShu orada: 🧮 Matematik misollar yecha olaman (2+2, 10*5)\n🎮 O'yin o'ynay olaman (tosh, latifa)"

    best_score = 0
    best_answer = None
    for item in knowledge:
        item_q = item.get("question", "").lower()
        item_words = set(re.findall(r'\w+', item_q))
        if item.get("category"):
            item_words.update(re.findall(r'\w+', item["category"].lower()))
        # To'g'ridan-to'g'ri moslik
        if q_lower in item_q or item_q in q_lower:
            return item["answer"]
        # So'z moslik hisoblash
        common = q_words & item_words
        if common:
            score = len(common) / max(len(q_words), 1) * 100
            score += sum(2 for w in common if len(w) > 3)
            if score > best_score:
                best_score = score
                best_answer = item["answer"]

    if best_score >= 25 and best_answer:
        return best_answer

    return f"Hmm, {name}, bu savolga hozircha javobim yo'q. 🤔\n\n💡 Quyidagi mavzularda suhbatlashishimiz mumkin:\n• 🌐 HTML: \"div nima\", \"img tegi\", \"table qanday\"\n• 🎨 CSS: \"flexbox nima\", \"margin padding\", \"display\"\n• ✨ Emmet: \"div*10 nima\", \"ul>li*5\", \"emmet nima\"\n• 🧮 Matematik: 2+2, 100/4, (5+3)*2\n• 🎮 O'yin: tosh, latifa, son ber\n\n📚 Yoki O'qitish tugmasi orqali menga yangi bilim bering!"

# ── Suhbat tarixi (har foydalanuvchi uchun alohida) ───────────────────────
def _load_chat_history(user_id):
    """Foydalanuvchining suhbat tarixini yuklaydi."""
    hist_file = AI_DATA_DIR / f"history_{user_id}.json"
    if not hist_file.exists():
        return []
    try:
        with open(hist_file, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def _save_chat_message(user_id, username, question, answer):
    """Yangi xabarni suhbat tarixiga qo'shadi."""
    hist_file = AI_DATA_DIR / f"history_{user_id}.json"
    history = _load_chat_history(user_id)
    history.append({
        "q": question,
        "a": answer[:1000],
        "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    })
    # Maksimal 200 ta xabar saqlash
    if len(history) > 200:
        history = history[-200:]
    try:
        with open(hist_file, "w", encoding="utf-8") as f:
            json.dump(history, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

# ── API endpointlari ──────────────────────────────────────────────────────
@app.route("/api/ai/ask", methods=["POST"])
@user_req
def api_ai_ask():
    d = request.get_json() or {}
    question = (d.get("question") or "").strip()
    if not question:
        return jsonify({"answer": "Savol bo'sh"})
    # Haqoratli so'z tekshiruvi
    if _contains_profanity(question):
        custom_resp = _load_badword_responses()
        if custom_resp:
            return jsonify({"answer": custom_resp})
        return jsonify({"answer": "⚠️ Iltimos, hurmatli muloqot qiling."})
    username = session.get("username", "")
    user_id = session.get("user_id", 0)
    # Suhbat tarixini yuklash
    history = _load_chat_history(user_id)
    answer = _ai_find_answer(question, username, history)
    # Suhbatni saqlash
    _save_chat_message(user_id, username, question, answer)
    return jsonify({"answer": answer})

@app.route("/api/ai/history")
@user_req
def api_ai_history():
    """Foydalanuvchining suhbat tarixini qaytaradi."""
    user_id = session.get("user_id", 0)
    history = _load_chat_history(user_id)
    return jsonify({"history": history[-50:]})  # oxirgi 50 ta

@app.route("/api/ai/history/clear", methods=["POST"])
@user_req
def api_ai_history_clear():
    """Suhbat tarixini tozalash."""
    user_id = session.get("user_id", 0)
    hist_file = AI_DATA_DIR / f"history_{user_id}.json"
    if hist_file.exists():
        hist_file.unlink()
    return jsonify({"ok": True})

@app.route("/api/ai/train", methods=["POST"])
@user_req
def api_ai_train():
    d = request.get_json() or {}
    train_type = d.get("type", "qa")  # "qa", "topic", "word", "badword"
    # Haqoratli so'z tekshiruvi (badword turida tekshirmaymiz — chunki o'zi qo'shilmoqda)
    if train_type != "badword":
        for field in ("question", "answer", "topic", "info"):
            val = d.get(field, "")
            if val and _contains_profanity(val):
                return jsonify({"ok": False, "error": "⚠️ Haqoratli so'z aniqlandi!"})
    if train_type == "badword":
        # Haqoratli so'z qo'shish / javob o'zgartirish
        word = (d.get("word") or "").strip().lower()
        response = (d.get("response") or "").strip()
        words = _load_badwords()
        if word and word not in words:
            words.append(word)
        if response or word:
            old_resp = _load_badword_responses()
            _save_badwords_data(words, response or old_resp)
        return jsonify({"ok": True, "words": words})
    if train_type == "word":
        # Savol so'zi qo'shish
        word = (d.get("word") or "").strip().lower()
        if not word:
            return jsonify({"ok": False, "error": "So'z kiriting"})
        words = _load_question_words()
        if word not in words:
            words.append(word)
            _save_question_words(words)
        return jsonify({"ok": True, "words": words})
    elif train_type == "topic":
        # Mavzu + ma'lumot qo'shish
        topic = (d.get("topic") or "").strip()
        info = (d.get("info") or "").strip()
        if not topic or not info:
            return jsonify({"ok": False, "error": "Mavzu va ma'lumot majburiy"})
        topics = _load_ai_topics()
        new_id = max([t.get("id", 0) for t in topics], default=0) + 1
        topics.append({"id": new_id, "topic": topic, "info": info,
                       "added_by": session.get("username", ""), "added_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")})
        _save_ai_topics(topics)
        audit("ai_train_topic", "topic", new_id, topic[:80])
        return jsonify({"ok": True, "id": new_id})
    else:
        # Oddiy savol-javob
        question = (d.get("question") or "").strip()
        answer = (d.get("answer") or "").strip()
        category = (d.get("category") or "").strip()
        if not question or not answer:
            return jsonify({"ok": False, "error": "Savol va javob majburiy"})
        knowledge = _load_ai_knowledge()
        new_id = max([item.get("id", 0) for item in knowledge], default=0) + 1
        knowledge.append({"id": new_id, "question": question, "answer": answer, "category": category,
                          "added_by": session.get("username", ""), "added_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")})
        _save_ai_knowledge(knowledge)
        audit("ai_train", "knowledge", new_id, question[:80])
        return jsonify({"ok": True, "id": new_id})

@app.route("/api/ai/knowledge")
@user_req
def api_ai_knowledge():
    knowledge = _load_ai_knowledge()
    topics = _load_ai_topics()
    words = _load_question_words()
    badwords = _load_badwords()
    badword_response = _load_badword_responses()
    return jsonify({"items": knowledge, "topics": topics, "words": words,
                    "badwords": badwords, "badword_response": badword_response})

@app.route("/api/ai/knowledge/<int:kid>", methods=["DELETE"])
@user_req
def api_ai_knowledge_delete(kid):
    knowledge = _load_ai_knowledge()
    knowledge = [item for item in knowledge if item.get("id") != kid]
    _save_ai_knowledge(knowledge)
    return jsonify({"ok": True})

@app.route("/api/ai/topics/<int:tid>", methods=["DELETE"])
@user_req
def api_ai_topic_delete(tid):
    topics = _load_ai_topics()
    topics = [t for t in topics if t.get("id") != tid]
    _save_ai_topics(topics)
    return jsonify({"ok": True})

@app.route("/api/ai/words/<word>", methods=["DELETE"])
@user_req
def api_ai_word_delete(word):
    words = _load_question_words()
    words = [w for w in words if w != word]
    _save_question_words(words)
    return jsonify({"ok": True})

@app.route("/api/ai/badwords/<word>", methods=["DELETE"])
@user_req
def api_ai_badword_delete(word):
    words = _load_badwords()
    words = [w for w in words if w != word]
    resp = _load_badword_responses()
    _save_badwords_data(words, resp)
    return jsonify({"ok": True})


# ── Terminal / Shell (xterm.js uchun backend) ──────────────────────────────
@app.route("/api/terminal/exec", methods=["POST"])
@admin_req
def terminal_exec():
    """Admin uchun server terminalida buyruq bajarish (xavfsizlik: faqat admin)."""
    d = request.get_json() or {}
    cmd = (d.get("command") or "").strip()
    if not cmd:
        return jsonify({"ok": False, "error": "Buyruq bo'sh"})
    # Xavfli buyruqlarni bloklash
    dangerous = ["rm -rf /", "mkfs", "dd if=", ":(){", "fork bomb", "shutdown", "reboot", "halt"]
    for dng in dangerous:
        if dng in cmd.lower():
            return jsonify({"ok": False, "error": "Bu buyruq taqiqlangan"})
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=10, cwd=os.getcwd())
        output = result.stdout + result.stderr
        audit("terminal_exec", "command", None, cmd[:200])
        return jsonify({"ok": True, "output": output[:5000], "returncode": result.returncode})
    except subprocess.TimeoutExpired:
        return jsonify({"ok": False, "error": "Buyruq 10 sekundda yakunlanmadi (timeout)"})
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)[:300]})



# ── Komponent kutubxonasi (Bootstrap/Tailwind) ─────────────────────────────
@app.route("/api/components")
@user_req
def api_components():
    """Tayyor HTML komponentlarni qaytaradi."""
    components = [
        {"id": "nav-bootstrap", "name": "Navbar (Bootstrap)", "category": "Bootstrap",
         "code": '<nav class="navbar navbar-expand-lg navbar-dark bg-dark">\n  <div class="container">\n    <a class="navbar-brand" href="#">Logo</a>\n    <button class="navbar-toggler" data-bs-toggle="collapse" data-bs-target="#nav1"><span class="navbar-toggler-icon"></span></button>\n    <div class="collapse navbar-collapse" id="nav1">\n      <ul class="navbar-nav ms-auto"><li class="nav-item"><a class="nav-link" href="#">Bosh sahifa</a></li><li class="nav-item"><a class="nav-link" href="#">Haqida</a></li></ul>\n    </div>\n  </div>\n</nav>'},
        {"id": "card-bootstrap", "name": "Card (Bootstrap)", "category": "Bootstrap",
         "code": '<div class="card" style="width:18rem">\n  <img src="https://via.placeholder.com/300x200" class="card-img-top" alt="...">\n  <div class="card-body">\n    <h5 class="card-title">Sarlavha</h5>\n    <p class="card-text">Qisqa tavsif matni.</p>\n    <a href="#" class="btn btn-primary">Batafsil</a>\n  </div>\n</div>'},
        {"id": "hero-bootstrap", "name": "Hero Section (Bootstrap)", "category": "Bootstrap",
         "code": '<section class="bg-dark text-white py-5">\n  <div class="container text-center">\n    <h1 class="display-4">Xush kelibsiz!</h1>\n    <p class="lead">Bu yerda asosiy matn joylashadi.</p>\n    <a href="#" class="btn btn-primary btn-lg mt-3">Boshlash</a>\n  </div>\n</section>'},
        {"id": "form-bootstrap", "name": "Form (Bootstrap)", "category": "Bootstrap",
         "code": '<form class="p-4">\n  <div class="mb-3"><label class="form-label">Email</label><input type="email" class="form-control" placeholder="email@example.com"></div>\n  <div class="mb-3"><label class="form-label">Parol</label><input type="password" class="form-control"></div>\n  <button type="submit" class="btn btn-primary">Yuborish</button>\n</form>'},
        {"id": "nav-tailwind", "name": "Navbar (Tailwind)", "category": "Tailwind",
         "code": '<nav class="bg-gray-800 p-4">\n  <div class="max-w-7xl mx-auto flex justify-between items-center">\n    <a href="#" class="text-white font-bold text-xl">Logo</a>\n    <div class="space-x-4"><a href="#" class="text-gray-300 hover:text-white">Bosh sahifa</a><a href="#" class="text-gray-300 hover:text-white">Haqida</a></div>\n  </div>\n</nav>'},
        {"id": "card-tailwind", "name": "Card (Tailwind)", "category": "Tailwind",
         "code": '<div class="max-w-sm rounded overflow-hidden shadow-lg bg-white">\n  <img class="w-full" src="https://via.placeholder.com/300x200" alt="">\n  <div class="px-6 py-4">\n    <div class="font-bold text-xl mb-2">Sarlavha</div>\n    <p class="text-gray-700 text-base">Tavsif matni.</p>\n  </div>\n  <div class="px-6 pt-4 pb-2"><span class="bg-gray-200 rounded-full px-3 py-1 text-sm font-semibold text-gray-700">#tag1</span></div>\n</div>'},
        {"id": "hero-tailwind", "name": "Hero (Tailwind)", "category": "Tailwind",
         "code": '<section class="bg-gradient-to-r from-purple-600 to-indigo-600 text-white py-20">\n  <div class="max-w-4xl mx-auto text-center">\n    <h1 class="text-5xl font-bold mb-4">Xush kelibsiz!</h1>\n    <p class="text-xl mb-8">Loyihangiz uchun zamonaviy dizayn.</p>\n    <a href="#" class="bg-white text-purple-600 px-8 py-3 rounded-full font-bold hover:bg-gray-100">Boshlash</a>\n  </div>\n</section>'},
        {"id": "footer", "name": "Footer", "category": "Umumiy",
         "code": '<footer style="background:#1a1a2e;color:#aaa;padding:30px 20px;text-align:center;margin-top:40px">\n  <p>&copy; 2025 Loyiha nomi. Barcha huquqlar himoyalangan.</p>\n  <div style="margin-top:10px"><a href="#" style="color:#7c6fff;margin:0 8px">GitHub</a><a href="#" style="color:#7c6fff;margin:0 8px">Telegram</a></div>\n</footer>'},
        {"id": "grid-css", "name": "CSS Grid Layout", "category": "Umumiy",
         "code": '<div style="display:grid;grid-template-columns:repeat(3,1fr);gap:16px;padding:20px">\n  <div style="background:#1c2136;border-radius:8px;padding:20px;color:#fff">Block 1</div>\n  <div style="background:#1c2136;border-radius:8px;padding:20px;color:#fff">Block 2</div>\n  <div style="background:#1c2136;border-radius:8px;padding:20px;color:#fff">Block 3</div>\n</div>'},
        {"id": "pricing", "name": "Pricing Table", "category": "Umumiy",
         "code": '<div style="display:flex;gap:20px;justify-content:center;padding:40px;flex-wrap:wrap">\n  <div style="background:#1c2136;border:1px solid #252d45;border-radius:12px;padding:30px;width:250px;text-align:center;color:#fff"><h3>Bepul</h3><p style="font-size:2rem;font-weight:700;color:#7c6fff">$0</p><p style="color:#888">1 loyiha<br>100MB joy</p><button style="background:#7c6fff;color:#fff;border:none;padding:10px 24px;border-radius:6px;cursor:pointer;margin-top:12px">Tanlash</button></div>\n  <div style="background:#1c2136;border:2px solid #7c6fff;border-radius:12px;padding:30px;width:250px;text-align:center;color:#fff"><h3>Pro</h3><p style="font-size:2rem;font-weight:700;color:#22d3a0">$9</p><p style="color:#888">10 loyiha<br>5GB joy</p><button style="background:#22d3a0;color:#000;border:none;padding:10px 24px;border-radius:6px;cursor:pointer;margin-top:12px;font-weight:700">Tanlash</button></div>\n</div>'},
    ]
    return jsonify({"components": components})

# ── Color Picker API ────────────────────────────────────────────────────────
@app.route("/api/color/palette")
@user_req
def color_palette():
    """Ranglar palitrasini qaytaradi."""
    palettes = {
        "Material": ["#F44336","#E91E63","#9C27B0","#673AB7","#3F51B5","#2196F3","#03A9F4","#00BCD4","#009688","#4CAF50","#8BC34A","#CDDC39","#FFEB3B","#FFC107","#FF9800","#FF5722"],
        "Pastel": ["#FFB3BA","#FFDFBA","#FFFFBA","#BAFFC9","#BAE1FF","#E8BAFF","#FFC8DD","#BDE0FE","#A2D2FF","#CDB4DB"],
        "Dark": ["#0d0f18","#161929","#1c2136","#252d45","#7c6fff","#22d3a0","#f05d5d","#f5c518","#5c6890","#d4daf0"],
        "Gradient": ["linear-gradient(135deg,#667eea,#764ba2)","linear-gradient(135deg,#f093fb,#f5576c)","linear-gradient(135deg,#4facfe,#00f2fe)","linear-gradient(135deg,#43e97b,#38f9d7)","linear-gradient(135deg,#fa709a,#fee140)"],
    }
    return jsonify({"palettes": palettes})


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║              BACKEND ENGINE — LOYIHA ICHIDAGI SERVERLESS FUNKSIYALAR     ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def project_db_path(puuid):
    safe = re.sub(r"[^a-zA-Z0-9-]", "", puuid)
    return PROJECT_DB_DIR / f"{safe}.db"

def ensure_project_db(puuid):
    p = project_db_path(puuid)
    if not p.exists():
        conn = sqlite3.connect(str(p))
        conn.close()
    return p

class SafeDB:
    """Foydalanuvchi kodiga beriladigan cheklangan SQL interfeysi."""
    def __init__(self, db_path):
        self._conn = sqlite3.connect(str(db_path), timeout=5)
        self._conn.row_factory = sqlite3.Row
        self._cur = self._conn.cursor()

    def _check(self, sql):
        if ";" in sql.strip().rstrip(";"):
            raise ValueError("Bir chaqiruvda faqat bitta SQL buyrug'iga ruxsat")
        if _SQL_FORBIDDEN.search(sql):
            raise ValueError("Bu SQL buyrug'i taqiqlangan")

    def execute(self, sql, params=()):
        self._check(sql)
        self._cur.execute(sql, tuple(params))
        return self

    def fetchone(self):
        r = self._cur.fetchone()
        return dict(r) if r else None

    def fetchall(self):
        return [dict(r) for r in self._cur.fetchall()]

    def commit(self):
        self._conn.commit()

    def close(self):
        try:
            self._conn.commit()
            self._conn.close()
        except Exception:
            pass

def _guarded_import(name, *args, **kwargs):
    root = name.split(".")[0]
    if root not in ALLOWED_IMPORTS:
        raise ImportError(f"'{name}' moduliga ruxsat yo'q (whitelist: {sorted(ALLOWED_IMPORTS)})")
    return __import__(name, *args, **kwargs)

def _build_restricted_globals():
    g = dict(safe_globals)
    g["__builtins__"] = dict(safe_builtins)
    g["__builtins__"]["__import__"] = _guarded_import
    g["_getiter_"] = default_guarded_getiter
    g["_iter_unpack_sequence_"] = guarded_iter_unpack_sequence
    g["_write_"] = full_write_guard
    for name in ("len", "range", "enumerate", "zip", "sorted", "min", "max",
                 "sum", "abs", "round", "isinstance", "str", "int", "float",
                 "bool", "list", "dict", "set", "tuple"):
        g["__builtins__"][name] = __builtins__[name] if isinstance(__builtins__, dict) else getattr(__builtins__, name)
    return g

def compile_user_code(code_str):
    if not RESTRICTED_OK:
        raise RuntimeError("RestrictedPython o'rnatilmagan: pip install RestrictedPython")
    byte_code = compile_restricted(code_str, filename="<backend-handler>", mode="exec")
    return byte_code

def _child_worker(conn, code_str, request_json, db_path):
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_CPU, (EXEC_TIMEOUT_SEC + 1, EXEC_TIMEOUT_SEC + 1))
        resource.setrlimit(resource.RLIMIT_AS, (MEM_LIMIT_MB * 1024 * 1024, MEM_LIMIT_MB * 1024 * 1024))
    except Exception:
        pass
    db = None
    try:
        byte_code = compile_user_code(code_str)
        ns = _build_restricted_globals()
        exec(byte_code, ns)
        handler = ns.get("handler")
        if not callable(handler):
            raise ValueError("Kodda `def handler(request_json, db):` funksiyasi topilmadi")
        db = SafeDB(db_path)
        result = handler(request_json, db)
        json.dumps(result)
        conn.send({"ok": True, "result": result})
    except Exception as e:
        conn.send({"ok": False, "error": f"{type(e).__name__}: {e}"})
    finally:
        if db:
            db.close()
        conn.close()

def run_user_backend(code_str, request_json, db_path, timeout=EXEC_TIMEOUT_SEC):
    t0 = time.time()
    parent_conn, child_conn = mp.Pipe()
    proc = mp.Process(target=_child_worker, args=(child_conn, code_str, request_json, str(db_path)))
    proc.start()
    proc.join(timeout)
    duration_ms = int((time.time() - t0) * 1000)
    if proc.is_alive():
        proc.terminate()
        proc.join(1)
        if proc.is_alive():
            proc.kill()
        return False, f"Vaqt tugadi ({timeout}s ichida yakunlanmadi)", duration_ms
    if parent_conn.poll():
        data = parent_conn.recv()
        if data.get("ok"):
            return True, data.get("result"), duration_ms
        return False, data.get("error", "Noma'lum xato"), duration_ms
    return False, "Protsessdan javob kelmadi (kutilmagan xato)", duration_ms

def _be_check_rate_limit(user_id):
    cutoff = (datetime.now() - timedelta(minutes=1)).strftime("%Y-%m-%d %H:%M:%S")
    row = q1("SELECT COUNT(*) c FROM backend_rate_limit WHERE user_id=? AND called_at>?", (user_id, cutoff))
    if row and row["c"] >= RATE_LIMIT_PER_MIN:
        return False
    db_exec("INSERT INTO backend_rate_limit (user_id) VALUES (?)", (user_id,), fetch=False)
    return True

def _be_log_exec(project_id, user_id, path, duration_ms, ok, error=""):
    db_exec("INSERT INTO backend_exec_logs (project_id,user_id,path,duration_ms,ok,error) VALUES (?,?,?,?,?,?)",
            (project_id, user_id, path, duration_ms, 1 if ok else 0, (error or "")[:500]), fetch=False)
    old = db_exec("SELECT id FROM backend_exec_logs ORDER BY id DESC LIMIT -1 OFFSET ?", (HISTORY_LOG_KEEP,)) or []
    for r in old:
        db_exec("DELETE FROM backend_exec_logs WHERE id=?", (r["id"],), fetch=False)

def _setup_backend_tables():
    """Backend uchun kerakli jadvallarni yaratadi."""
    be_stmts = [
        """CREATE TABLE IF NOT EXISTS project_backend_routes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            path TEXT NOT NULL,
            method TEXT DEFAULT 'GET',
            code TEXT NOT NULL,
            updated_at TEXT DEFAULT (datetime('now')),
            UNIQUE(project_id, path, method))""",
        """CREATE TABLE IF NOT EXISTS backend_exec_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER,
            user_id INTEGER,
            path TEXT,
            duration_ms INTEGER,
            ok INTEGER,
            error TEXT,
            created_at TEXT DEFAULT (datetime('now')))""",
        """CREATE TABLE IF NOT EXISTS backend_rate_limit (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            called_at TEXT DEFAULT (datetime('now')))""",
    ]
    for s in be_stmts:
        db_exec(s, fetch=False)
    _ensure_column("projects", "backend_enabled", "INTEGER DEFAULT 0")

def _backend_globally_enabled():
    return RESTRICTED_OK and get_setting("backend_enabled", "0") == "1"

def _backend_project_or_403(puuid, need_write=False):
    proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
    if not proj:
        abort(404)
    is_owner = proj["owner_id"] == session.get("user_id")
    if not is_owner and not session.get("admin"):
        abort(403)
    if need_write and role_rank(session.get("role")) < ROLE_RANK["user"]:
        abort(403)
    return proj

def _register_backend_routes():
    """Backend marshrutlarini Flask app ga ro'yxatdan o'tkazadi."""

    @app.route("/admin/backend/toggle", methods=["POST"])
    @admin_req
    def backend_admin_toggle():
        if not RESTRICTED_OK:
            return redirect(request.referrer or "/admin/settings")
        cur = get_setting("backend_enabled", "0")
        set_setting("backend_enabled", "0" if cur == "1" else "1")
        return redirect(request.referrer or "/admin/settings")

    @app.route("/admin/backend/logs")
    @admin_req
    def backend_admin_logs():
        rows = db_exec("""SELECT l.*, p.name as pname, u.username FROM backend_exec_logs l
                           LEFT JOIN projects p ON l.project_id=p.id
                           LEFT JOIN users u ON l.user_id=u.id
                           ORDER BY l.id DESC LIMIT 200""") or []
        tr = "".join(f"""<tr>
          <td>{r.get('pname') or '—'}</td><td>{r.get('username') or '—'}</td>
          <td><code style="font-size:.72rem">{r['path']}</code></td>
          <td>{r['duration_ms']} ms</td>
          <td><span class="bx {'xg' if r['ok'] else 'xr'}">{'OK' if r['ok'] else 'Xato'}</span></td>
          <td class="tm" style="font-size:.72rem">{(r.get('error') or '')[:80]}</td>
          <td class="tm" style="font-size:.72rem">{str(r['created_at'])[:19]}</td>
        </tr>""" for r in rows)
        status = ("✅ RestrictedPython o'rnatilgan" if RESTRICTED_OK
                  else "⚠️ RestrictedPython O'RNATILMAGAN — pip install RestrictedPython")
        on = get_setting("backend_enabled", "0") == "1"
        body = f"""
        <div class="fl mb"><h2 style="color:#fff">🐍 Backend — ijro loglari</h2>
          <span class="bx {'xg' if RESTRICTED_OK else 'xr'} mla">{status}</span></div>
        <form method="POST" action="/admin/backend/toggle" class="mb">{csrf_field()}
          <button class="btn {'br' if on else 'bg'} bsm" {'' if RESTRICTED_OK else 'disabled'}>
            {"🔴 Global backendni o'chirish" if on else "🟢 Global backendni yoqish"}</button>
        </form>
        <div class="card" style="padding:0"><div class="tw">
          <table><thead><tr><th>Loyiha</th><th>Foydalanuvchi</th><th>Yo'l</th><th>Vaqt</th>
          <th>Holat</th><th>Xato</th><th>Vaqt belgisi</th></tr></thead>
          <tbody>{tr or "<tr><td colspan=7 style='text-align:center;color:var(--mt);padding:16px'>Hali chaqiruv yo'q</td></tr>"}</tbody></table>
        </div></div>"""
        return _pg("Backend loglari", body, "backend")

    @app.route("/projects/<puuid>/backend/toggle", methods=["POST"])
    @user_req
    @write_req
    def backend_project_toggle(puuid):
        proj = _backend_project_or_403(puuid, need_write=True)
        if not _backend_globally_enabled():
            abort(403)
        new_val = 0 if proj.get("backend_enabled") else 1
        db_exec("UPDATE projects SET backend_enabled=? WHERE id=?", (new_val, proj["id"]), fetch=False)
        if new_val:
            ensure_project_db(puuid)
        return redirect(request.referrer or "/projects")

    @app.route("/editor/backend/routes/<puuid>", methods=["GET", "POST"])
    @user_req
    def backend_routes_list(puuid):
        proj = _backend_project_or_403(puuid)
        if request.method == "GET":
            rows = db_exec("SELECT id,path,method,updated_at FROM project_backend_routes WHERE project_id=? ORDER BY path",
                           (proj["id"],)) or []
            return jsonify({"routes": rows, "backend_enabled": bool(proj.get("backend_enabled")),
                             "global_enabled": _backend_globally_enabled()})
        if role_rank(session.get("role")) < ROLE_RANK["user"]:
            return jsonify({"ok": False, "error": "Ruxsat yo'q"}), 403
        if not proj.get("backend_enabled"):
            return jsonify({"ok": False, "error": "Bu loyihada backend yoqilmagan"}), 403
        d = request.get_json() or {}
        path = "/" + (d.get("path") or "").strip().lstrip("/")
        method = (d.get("method") or "GET").upper()
        code = d.get("code", "")
        if method not in ("GET", "POST") or path == "/" or not code.strip():
            return jsonify({"ok": False, "error": "Noto'g'ri ma'lumot"}), 400
        db_exec("""INSERT INTO project_backend_routes (project_id,path,method,code) VALUES (?,?,?,?)
                   ON CONFLICT(project_id,path,method) DO UPDATE SET code=excluded.code, updated_at=datetime('now')""",
                (proj["id"], path, method, code), fetch=False)
        return jsonify({"ok": True})

    @app.route("/editor/backend/routes/<puuid>/<int:rid>", methods=["GET", "DELETE"])
    @user_req
    def backend_route_item(puuid, rid):
        proj = _backend_project_or_403(puuid)
        if request.method == "DELETE":
            if role_rank(session.get("role")) < ROLE_RANK["user"]:
                return jsonify({"ok": False}), 403
            db_exec("DELETE FROM project_backend_routes WHERE id=? AND project_id=?", (rid, proj["id"]), fetch=False)
            return jsonify({"ok": True})
        row = q1("SELECT * FROM project_backend_routes WHERE id=? AND project_id=?", (rid, proj["id"]))
        if not row:
            abort(404)
        return jsonify({"route": row})

    @app.route("/editor/backend/test/<puuid>/<int:rid>", methods=["POST"])
    @user_req
    @write_req
    def backend_route_test(puuid, rid):
        proj = _backend_project_or_403(puuid, need_write=True)
        row = q1("SELECT * FROM project_backend_routes WHERE id=? AND project_id=?", (rid, proj["id"]))
        if not row:
            abort(404)
        if not _backend_globally_enabled():
            return jsonify({"ok": False, "error": "Backend global o'chirilgan"}), 403
        test_input = (request.get_json() or {}).get("input", {})
        db_path = ensure_project_db(puuid)
        ok, payload, dur = run_user_backend(row["code"], test_input, db_path)
        _be_log_exec(proj["id"], session["user_id"], f"[TEST]{row['path']}", dur, ok, "" if ok else str(payload))
        return jsonify({"ok": ok, "result": payload if ok else None, "error": None if ok else payload, "duration_ms": dur})

    @app.route("/api/backend/<puuid>/<path:route_path>", methods=["GET", "POST"])
    def backend_run(puuid, route_path):
        if not _backend_globally_enabled():
            abort(403)
        if session.get("_guest"):
            abort(403)
        if mode_on("global"):
            abort(403)
        if "user_id" not in session:
            abort(401)
        proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
        if not proj or not proj.get("backend_enabled"):
            abort(404)
        path = "/" + route_path.lstrip("/")
        row = q1("SELECT * FROM project_backend_routes WHERE project_id=? AND path=? AND method=?",
                 (proj["id"], path, request.method))
        if not row:
            abort(404)
        if not _be_check_rate_limit(session["user_id"]):
            return jsonify({"error": f"Juda ko'p so'rov. Daqiqasiga maksimal {RATE_LIMIT_PER_MIN} marta chaqiring."}), 429
        payload_in = request.get_json(silent=True) or dict(request.args)
        db_path = ensure_project_db(puuid)
        ok, payload, dur = run_user_backend(row["code"], payload_in, db_path)
        _be_log_exec(proj["id"], session["user_id"], path, dur, ok, "" if ok else str(payload))
        if ok:
            return jsonify(payload)
        return jsonify({"error": payload}), 400

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║                     TERMINAL + MAIN                                       ║
# ╚══════════════════════════════════════════════════════════════════════════╝
def print_banner():
    print(_c("""
╔══════════════════════════════════════════════════════════════════════╗
║      ⬡  UNIVERSAL SERVER BOSHQARUV TIZIMI  v2.2  (SQLite)          ║
║      Python + Flask  |  Windows / Linux                             ║
║      + QR-kod · Monitoring · Qidiruv · Backup · Telegram · Emmet     ║
║      + CSRF · RBAC · API-kalitlar · 2FA · Guest rejim · Editor 2.0   ║
╚══════════════════════════════════════════════════════════════════════╗""",C))

def print_menu():
    print(f"""
  {_c('Rejimni tanlang:',W)}

  {_c('1',Y)}  🔒  Shaxsiy (localhost)   — faqat siz
  {_c('2',G)}  📡  LAN / WiFi            — bir xil tarmoqdagilar
  {_c('3',M)}  🌍  Global (Internet)     — ngrok orqali butun dunyo
  {_c('0',R)}  ❌  Chiqish
""")

def run_srv(host):
    import logging
    logging.getLogger("werkzeug").setLevel(logging.WARNING)
    app.run(host=host,port=CFG["PORT"],debug=False,use_reloader=False,threaded=True)

def show_info(mode):
    port=CFG["PORT"]; ip=local_ip(); ssid=get_ssid(); pub=_active_mode.get("url","")
    print("\n"+_c("─"*66,C))
    if mode=="private":
        url=f"http://127.0.0.1:{port}"
        print(_c("  🔒  SHAXSIY REJIM",Y)); print(_c("─"*66,C))
        print(f"\n  {_c('Sayt:',G)}      {_c(url,W)}")
        print(f"  {_c('Dashboard:',G)} {_c(url+'/dashboard',W)}")
        print(f"  {_c('Login:',Y)}     {CFG['ADMIN_USER']}  |  {_c('Parol:',Y)} {CFG['ADMIN_PASS']}")
        print(f"\n  {_c('+ Havola yaratish:',C)} /links/new — token oling")
        print(f"  {_c('Shaxsiy havola:',M)}  {url}/p/<TOKEN>")
        print(f"  {_c('Monitoring:',C)}      {url}/admin/monitor")
        print(f"\n  {_c('Faqat bu kompyuterdan kirish mumkin.',Y)}")
    elif mode=="lan":
        url=f"http://{ip}:{port}"
        print(_c("  📡  LAN REJIM",G)); print(_c("─"*66,C))
        print(f"\n  {_c('WiFi SSID:',G)}   {_c(ssid,W)}")
        print(f"  {_c('Manzil:',G)}      {_c(url,W)}")
        print(f"\n  {_c('Boshqa qurilmadan ulanish:',C)}")
        print(f"  1. {_c(ssid,W)} WiFi ga ulaning")
        print(f"  2. Brauzerda oching: {_c(url,W)}")
        print(f"  3. Yoki havola sahifasida QR-kodni skanerlang (📱)")
        if platform.system()=="Windows":
            print(f"\n  {_c('⚠  Windows Firewall ruxsat so\'rasa — Ha deng',Y)}")
    elif mode=="global":
        print(_c("  🌍  GLOBAL REJIM (ngrok)",M)); print(_c("─"*66,C))
        if pub:
            print(f"\n  {_c('✓ Ngrok faol!',G)}")
            print(f"  {_c('Ommaviy URL:',G)}  {_c(pub,W)}")
            print(f"  {_c('Dashboard:',G)}    {_c(pub+'/dashboard',W)}")
            print(f"\n  {_c('Bu havolani istaganingizga yuboring!',C)}")
        else:
            print(f"\n  {_c('✗ Ngrok ishlamadi.',R)}")
            print(f"  /modes sahifasida Ngrok Start tugmasini bosing")
            print(f"  yoki CFG[\"NGROK_TOKEN\"] ga token qo'ying.")
    print(_c("─"*66,C))
    print(f"\n  {_c('Toxtatish uchun: Ctrl+C',Y)}\n")

def main():
    print_banner()
    print(_c("\n  🗄  SQLite baza tayyorlanmoqda...",C))
    setup_db()
    print(_c("  ✓ Tayyor! Ma'lumotlar: server_data.db",G))
    if not PSUTIL_OK:
        print(_c("  ⚠  Monitoring uchun: pip install psutil",Y))
    if not QRCODE_OK:
        print(_c("  ⚠  QR-kod uchun: pip install qrcode[pil]",Y))
    threading.Thread(target=expiry_checker,daemon=True).start()
    threading.Thread(target=_uptime_checker,daemon=True).start()
    while True:
        print_menu()
        try:
            ch=input(f"  {_c('Tanlov (0-3):',W)} ").strip()
        except (KeyboardInterrupt,EOFError):
            print(f"\n  {_c('Xayr!',Y)}\n"); break
        if ch=="1":
            t=threading.Thread(target=run_srv,args=("127.0.0.1",),daemon=True)
            t.start(); time.sleep(0.8); show_info("private")
            try:
                while t.is_alive(): time.sleep(1)
            except KeyboardInterrupt:
                print(f"\n  {_c('Server toxtatildi.',Y)}")
        elif ch=="2":
            t=threading.Thread(target=run_srv,args=("0.0.0.0",),daemon=True)
            t.start(); time.sleep(0.8); show_info("lan")
            try:
                while t.is_alive(): time.sleep(1)
            except KeyboardInterrupt:
                print(f"\n  {_c('Server toxtatildi.',Y)}")
        elif ch=="3":
            if NGROK_OK:
                print(_c("\n  🚀 Ngrok tunnel ochilmoqda...",C))
                try:
                    if CFG["NGROK_TOKEN"]: _ngrok.set_auth_token(CFG["NGROK_TOKEN"])
                    global _ngrok_tunnel
                    _ngrok_tunnel=_ngrok.connect(CFG["PORT"],"http")
                    _active_mode["url"]=_ngrok_tunnel.public_url
                except Exception as e:
                    print(_c(f"  [ngrok xato] {e}",R))
            else:
                print(_c("  ⚠  pyngrok yo'q: pip install pyngrok",Y))
            t=threading.Thread(target=run_srv,args=("0.0.0.0",),daemon=True)
            t.start(); time.sleep(1); show_info("global")
            try:
                while t.is_alive(): time.sleep(1)
            except KeyboardInterrupt:
                print(f"\n  {_c('Server toxtatildi.',Y)}")
                if NGROK_OK:
                    try: _ngrok.kill()
                    except: pass
                _active_mode["url"]=None
        elif ch=="0":
            print(f"\n  {_c('Xayr!',Y)}\n"); break
        else:
            print(_c("  Noto'g'ri tanlov!",R))


_register_backend_routes()
if __name__=="__main__":
    main()
