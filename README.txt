╔══════════════════════════════════════╗
║      Bot Archivador v3.1             ║
║      Telegram → Nube (archive.org)   ║
╚══════════════════════════════════════╝

═══════════════════════════════════════
 REQUISITOS DEL SISTEMA
═══════════════════════════════════════
- Python 3.11 o superior
- p7zip  (para el comando 7z)
- yt-dlp (incluido en requirements.txt)

═══════════════════════════════════════
 INSTALACIÓN
═══════════════════════════════════════
1. Instala las dependencias:
   pip install -r requirements.txt

2. Instala p7zip en tu sistema:
   - Ubuntu/Debian: sudo apt install p7zip-full
   - macOS:         brew install p7zip
   - Windows:       descargar de https://www.7-zip.org

═══════════════════════════════════════
 VARIABLES DE ENTORNO REQUERIDAS
═══════════════════════════════════════
Configura estas variables antes de iniciar:

  TELEGRAM_BOT_TOKEN      → Token de @BotFather
  TELEGRAM_ADMIN_ID       → Tu ID numérico o @usuario de Telegram
  TELEGRAM_API_ID         → API ID de https://my.telegram.org
  TELEGRAM_API_HASH       → API Hash de https://my.telegram.org
  ARCHIVE_ORG_ACCESS_KEY  → Llave de acceso de archive.org
  ARCHIVE_ORG_SECRET_KEY  → Llave secreta de archive.org

═══════════════════════════════════════
 CÓMO EJECUTAR
═══════════════════════════════════════
  python3 bot.py

═══════════════════════════════════════
 FUNCIONALIDADES
═══════════════════════════════════════
  ✅ Archivos de Telegram hasta 2 GB (MTProto)
  ✅ YouTube con selector de calidad
  ✅ Playlists completas de YouTube
  ✅ Instagram, TikTok, Twitter/X
  ✅ Cualquier URL de descarga directa
  ✅ Compresión 7z nivel máximo (archivo único)
  ✅ Subida a la nube (archive.org)
  ✅ Enlace enviado en archivo .txt
  ✅ Cola de trabajos por usuario
  ✅ Sistema de cuotas diarias
  ✅ Aprobación/rechazo de acceso con botones
  ✅ Historial de subidas por usuario
  ✅ Cancelar tarea en curso
  ✅ Notificaciones al admin

═══════════════════════════════════════
 COMANDOS DEL BOT
═══════════════════════════════════════
  /start      Inicio y bienvenida
  /help       Comandos disponibles
  /status     Estado de la tarea actual
  /cancelar   Cancelar tarea en curso
  /historial  Últimas 10 subidas

  (Admin)
  /add_user   Agregar usuario por ID o @usuario
  /ban_user   Banear usuario
  /list_user  Ver todos los usuarios
  /set_cuota  Cambiar cuota diaria de un usuario
