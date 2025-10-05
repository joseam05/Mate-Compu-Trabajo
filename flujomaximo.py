import tkinter as tk
from tkinter import messagebox, filedialog
import json
import math
import random
import string


def ford_fulkerson(n, aristas, origen, destino):
    # Obtener la lista única y ordenada de nodos
    nodos = sorted(list(set([u for u,_,_ in aristas] + [v for _,v,_ in aristas])))
    
    if origen not in nodos or destino not in nodos:
        raise ValueError("El nodo origen o destino no está presente.")
        
    # Mapeo de IDs de nodo a índices de matriz
    idx = {nodo:i for i,nodo in enumerate(nodos)}
    rev = {i:nodo for nodo,i in idx.items()}

    N = len(nodos)
    capacidad = [[0]*N for _ in range(N)]
    for u,v,c in aristas:
        # Sumar capacidades si hay múltiples aristas entre los mismos nodos
        capacidad[idx[u]][idx[v]] += c

    flujo = [[0]*N for _ in range(N)]

    # Función DFS para encontrar un camino de aumento
    def dfs(u, t, visitado, padre):
        if u == t:
            return float("inf")
        visitado[u] = True
        for v in range(N):
            # Capacidad residual: capacidad original - flujo actual
            residual = capacidad[u][v] - flujo[u][v]
            if residual > 0 and not visitado[v]:
                padre[v] = u
                cuello = dfs(v, t, visitado, padre)
                if cuello > 0:
                    return min(cuello, residual)
        return 0

    s, t = idx[origen], idx[destino]
    flujo_maximo = 0
    
    # Bucle principal de Ford-Fulkerson
    while True:
        padre = [-1]*N
        visitado = [False]*N
        padre[s] = s
        
        aumento = dfs(s, t, visitado, padre)
        
        if aumento <= 0:
            break
            
        # Actualizar el flujo a lo largo del camino encontrado
        v = t
        while v != s:
            u = padre[v]
            flujo[u][v] += aumento
            flujo[v][u] -= aumento
            v = u
        flujo_maximo += aumento

    flujo_pares = {}
    for u in range(N):
        for v in range(N):
            if capacidad[u][v] > 0:
                f = flujo[u][v]
                # Solo guardar flujos mayores a 0 para visualización
                flujo_pares[(rev[u], rev[v])] = f if f > 0 else 0

    return flujo_maximo, flujo_pares, nodos

# ---------------------------------------
# GUI
# ---------------------------------------
RADIO_NODO = 20 # Nodos un poco más grandes
TAM_FLECHA = 10
ESPACIO_ARISTA = 14 # Más espacio para separar líneas bidireccionales


COLORES = {
    "fondo": "#0b1021",
    "panel": "#121933",
    "texto": "#a6a7a9",
    "nodo": "#2b3a67", 
    "nodo_origen": "#22b14c", 
    "nodo_destino": "#f44336", 
    "arista": "#aab2cf", 
    "arista_sat": "#ffcc00", 
    "arista_flujo_texto": "#ffffff",
    "cuadricula": "#1a2447",
}


BOTON_DEFAULT_BG = "#5c7cbe"  
BOTON_DEFAULT_ACT = "#7d97d1" 

class FlujoMaximoGUI:
    def __init__(self, raiz):
        self.raiz = raiz
        self.raiz.title("Flujo Máximo – Ford–Fulkerson (DFS) Estilo Moderno")
        self.raiz.configure(bg=COLORES["fondo"])
        self.raiz.minsize(1100, 650)

        # Estado del grafo
        self.nodos = {}
        self.aristas = [] # Lista de tuplas (u, v, capacidad)
        self.origen = None
        self.destino = None
        self.ultimo_flujo = None

        # Estado de interacción
        self.arrastrando = None
        self.desfase = (0,0)
        
        # Para la funcionalidad de varios ejemplos
        self.lista_ejemplos = []
        self.indice_ejemplo = -1

        self._construir_ui()
        
        # Canvas principal para dibujar el grafo
        self.canvas = tk.Canvas(self.raiz, bg=COLORES["fondo"], highlightthickness=0)
        self.canvas.pack(side="right", fill="both", expand=True)

        self._vincular_eventos_canvas()

    def _on_frame_configure(self, event):
        self.izquierda_canvas.configure(scrollregion=self.izquierda_canvas.bbox("all"))

    def _construir_ui(self):
        
        # --- Configuración del Panel de Control (Scrollable) ---
        scroll_container = tk.Frame(self.raiz, bg=COLORES["panel"], width=320)
        scroll_container.pack(side="left", fill="y", expand=False)

        scrollbar = tk.Scrollbar(scroll_container, orient="vertical")
        scrollbar.pack(side="right", fill="y")

        self.izquierda_canvas = tk.Canvas(scroll_container, bg=COLORES["panel"], yscrollcommand=scrollbar.set, highlightthickness=0)
        self.izquierda_canvas.pack(side="left", fill="y", expand=True)

        scrollbar.config(command=self.izquierda_canvas.yview)

        self.izquierda = tk.Frame(self.izquierda_canvas, bg=COLORES["panel"]) 
        self.izquierda_canvas.create_window((0, 0), window=self.izquierda, anchor="nw")
        self.izquierda.bind("<Configure>", self._on_frame_configure)
        
        # --- FIN Configuración del Scrollable Frame ---


        pad = {"padx": 12, "pady": 8}
        titulo = tk.Label(self.izquierda, text="Constructor de Flujo Máximo", fg=COLORES["texto"], bg=COLORES["panel"], font=("Arial", 14, "bold"))
        titulo.pack(fill="x", **pad)

        # --- Entrada de Nodo ---
        nodo_fr = tk.LabelFrame(self.izquierda, text="Agregar Nodo (Letra)", fg=COLORES["texto"], bg=COLORES["panel"], padx=10, pady=5)
        nodo_fr.pack(fill="x", padx=12, pady=6)
        self.nodo_id_entrada = self._crear_entrada(nodo_fr, "ID Nodo (e.g., G):")
        tk.Button(nodo_fr, text="Agregar Nodo", command=self.agregar_nodo_click, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=6)

        # --- Entrada de Arista ---
        arista_fr = tk.LabelFrame(self.izquierda, text="Agregar Arista", fg=COLORES["texto"], bg=COLORES["panel"], padx=10, pady=5)
        arista_fr.pack(fill="x", padx=12, pady=6)
        self.arista_u_entrada = self._crear_entrada(arista_fr, "u (Origen):")
        self.arista_v_entrada = self._crear_entrada(arista_fr, "v (Destino):")
        self.arista_c_entrada = self._crear_entrada(arista_fr, "Capacidad (c):")
        tk.Button(arista_fr, text="Agregar Arista", command=self.agregar_arista_click, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=6)

        # --- Origen / Destino ---
        st_fr = tk.LabelFrame(self.izquierda, text="Origen / Destino", fg=COLORES["texto"], bg=COLORES["panel"], padx=10, pady=5)
        st_fr.pack(fill="x", padx=12, pady=6)
        self.origen_entrada = self._crear_entrada(st_fr, "Origen (s):")
        self.destino_entrada = self._crear_entrada(st_fr, "Destino (t):")
        tk.Button(st_fr, text="Definir Origen (s)", command=self.definir_origen, bg=COLORES["nodo_origen"], fg=COLORES["texto"], activebackground="#27c655", relief="flat").pack(fill="x", pady=2)
        tk.Button(st_fr, text="Definir Destino (t)", command=self.definir_destino, bg=COLORES["nodo_destino"], fg=COLORES["texto"], activebackground="#ff5549", relief="flat").pack(fill="x", pady=2)

        # --- Ejecutar ---
        run_fr = tk.LabelFrame(self.izquierda, text="Ejecutar", fg=COLORES["texto"], bg=COLORES["panel"], padx=10, pady=5)
        run_fr.pack(fill="x", padx=12, pady=6)
        tk.Button(run_fr, text="Ejecutar Ford–Fulkerson", command=self.ejecutar_flujo_maximo, bg="#ffcc00", fg="#121933", activebackground="#ffdd33", font=("Arial", 10, "bold"), relief="flat").pack(fill="x", pady=6)

        # --- I/O y Ejemplos ---
        io_fr = tk.LabelFrame(self.izquierda, text="I/O y Ejemplos", fg=COLORES["texto"], bg=COLORES["panel"], padx=10, pady=5)
        io_fr.pack(fill="x", padx=12, pady=6)
        
        tk.Button(io_fr, text="Guardar JSON", command=self.guardar_json, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=4)
        tk.Button(io_fr, text="Cargar JSON", command=self.cargar_json, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=4)
        
        tk.Button(io_fr, text="Ejemplo (CLRS)", command=self.cargar_ejemplo, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=4)
        
        tk.Button(io_fr, text="Ejemplo Aleatorio (Ordenado)", command=self.cargar_ejemplo_aleatorio, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=4)
        tk.Button(io_fr, text="Varios Aleatorios (Ordenados)", command=self.cargar_varios_ejemplos, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(fill="x", pady=4)
        
        nav_fr = tk.Frame(io_fr, bg=COLORES["panel"])
        nav_fr.pack(fill="x", pady=2)
        tk.Button(nav_fr, text="← Anterior", command=self.ejemplo_anterior, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(side="left", expand=True, fill="x", padx=2)
        tk.Button(nav_fr, text="Siguiente →", command=self.ejemplo_siguiente, bg=BOTON_DEFAULT_BG, fg=COLORES["texto"], activebackground=BOTON_DEFAULT_ACT, relief="flat").pack(side="right", expand=True, fill="x", padx=2)
        
        tk.Button(io_fr, text="Limpiar Todo", command=self.limpiar_todo, bg="#6b7a99", fg=COLORES["texto"], activebackground="#7c8cb1", relief="flat").pack(fill="x", pady=8)

        # --- Estado ---
        self.estado = tk.Label(self.izquierda, text="Listo.", fg=COLORES["texto"], bg=COLORES["panel"], anchor="w", font=("Arial", 10))
        self.estado.pack(fill="x", padx=12, pady=(10, 5))


    def _crear_entrada(self, padre, etiqueta):
        f = tk.Frame(padre, bg=COLORES["panel"])
        f.pack(fill="x", pady=2)
        tk.Label(f, text=etiqueta, fg=COLORES["texto"], bg=COLORES["panel"]).pack(anchor="w")
        e = tk.Entry(f, bg="#202c4b", fg=COLORES["texto"], insertbackground=COLORES["texto"], relief="flat")
        e.pack(fill="x")
        return e

    def _vincular_eventos_canvas(self):
        if hasattr(self, 'canvas'):
            self.canvas.bind("<Configure>", lambda e: self.redibujar())
            self.canvas.bind("<Button-1>", self._on_click)
            self.canvas.bind("<B1-Motion>", self._on_drag)
            self.canvas.bind("<ButtonRelease-1>", self._on_release)

    def agregar_nodo_click(self):
        nid = self.nodo_id_entrada.get().strip().upper() # Convertir a mayúscula para consistencia
        if not nid or len(nid) != 1 or not nid.isalpha():
            messagebox.showerror("Error", "El ID del nodo debe ser una única letra (A-Z).")
            return
        if nid in self.nodos:
            messagebox.showwarning("Advertencia", f"El nodo '{nid}' ya existe.")
            return
            
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        x = random.randint(50, max(60, w-50))
        y = random.randint(50, max(60, h-50))
        
        self.nodos[nid] = {"x": x, "y": y}
        self.nodo_id_entrada.delete(0, tk.END) 
        self.redibujar()

    def agregar_arista_click(self):
        u, v, c = self.arista_u_entrada.get().strip().upper(), self.arista_v_entrada.get().strip().upper(), self.arista_c_entrada.get().strip()
        
        if u not in self.nodos or v not in self.nodos:
            messagebox.showerror("Error", "Los nodos de origen o destino no existen.")
            return
        try:
            capacidad = float(c)
            if capacidad <= 0: raise ValueError
        except:
            messagebox.showerror("Error", "La capacidad debe ser un número positivo.")
            return
            
        self.aristas.append((u, v, capacidad))
        self.arista_u_entrada.delete(0, tk.END)
        self.arista_v_entrada.delete(0, tk.END)
        self.arista_c_entrada.delete(0, tk.END)
        self.redibujar()

    def definir_origen(self):
        o = self.origen_entrada.get().strip().upper()
        if o in self.nodos:
            self.origen = o
            self.redibujar()
        else:
            messagebox.showwarning("Advertencia", f"El nodo '{o}' no existe para ser definido como origen.")

    def definir_destino(self):
        d = self.destino_entrada.get().strip().upper()
        if d in self.nodos:
            self.destino = d
            self.redibujar()
        else:
            messagebox.showwarning("Advertencia", f"El nodo '{d}' no existe para ser definido como destino.")

    def ejecutar_flujo_maximo(self):
        if not self.origen or not self.destino:
            messagebox.showerror("Error", "Debe definir un nodo Origen (s) y un Destino (t).")
            return
        if self.origen == self.destino:
            messagebox.showerror("Error", "El Origen y el Destino no pueden ser el mismo nodo.")
            return
            
        # Agrupar capacidades si hay aristas duplicadas
        agg = {}
        for u,v,c in self.aristas:
            agg[(u,v)] = agg.get((u,v), 0.0) + c
        aristas_unidas = [(u,v,c) for (u,v),c in agg.items()]

        try:
            flujo_maximo, flujo_pares, _ = ford_fulkerson(len(self.nodos), aristas_unidas, self.origen, self.destino)
            self.ultimo_flujo = {"valor": flujo_maximo, "pares": flujo_pares, "capacidad": agg}
            self.estado["text"] = f"Flujo Máximo = {flujo_maximo}"
            self.redibujar()
            messagebox.showinfo("Resultado", f"Ford–Fulkerson (DFS)\nFlujo máximo = {flujo_maximo}")
        except ValueError as e:
             messagebox.showerror("Error de Cálculo", str(e))
        except Exception as e:
            messagebox.showerror("Error Inesperado", f"Ocurrió un error durante el cálculo: {e}")


    def _generar_layout_circular(self, n_nodos):
        """Genera posiciones de nodo en un círculo para un layout limpio."""
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        center_x, center_y = max(w / 2, 250), max(h / 2, 250)
        radius = min(w, h) / 2.5 # Radio para que se ajuste bien
        
        nodos_coords = {}
        letras = string.ascii_uppercase[:n_nodos]
        
        for i, nid in enumerate(letras):
            # Calcular ángulo para posicionar nodos uniformemente en un círculo
            angle = 2 * math.pi * i / n_nodos
            # Empezar desde arriba (offset de -pi/2) y girar en sentido horario
            x = center_x + radius * math.cos(angle - math.pi/2) 
            y = center_y + radius * math.sin(angle - math.pi/2)
            nodos_coords[nid] = {"x": x, "y": y}
            
        return nodos_coords, letras[0], letras[-1]

    def cargar_ejemplo_aleatorio(self):
        self.limpiar_todo(confirmar=False)
        
        n = random.randint(5, 7) # Número de nodos entre 5 y 7
        
        # 1. Generar layout circular y obtener IDs con letras
        self.nodos, self.origen, self.destino = self._generar_layout_circular(n)
        letras = list(self.nodos.keys())
        
        aristas = []
        
        # 2. Garantizar una ruta de A al último nodo (conectividad)
        for i in range(n - 1):
            u, v = letras[i], letras[i + 1]
            capacidad = random.randint(10, 30) 
            aristas.append((u, v, capacidad))

        # 3. Agregar aristas aleatorias adicionales
        for i in range(n):
            for j in range(n):
                u, v = letras[i], letras[j]
                # Evitar auto-bucles y mantener una probabilidad razonable de aristas adicionales
                if u != v and random.random() < 0.4: 
                    # Evitar duplicar la arista base forzada
                    if (u, v) not in [(letras[k], letras[k+1]) for k in range(n-1)]:
                        capacidad = random.randint(1, 15)
                        aristas.append((u, v, capacidad))

        # Agrupar capacidades si hay aristas duplicadas
        agg = {}
        for u,v,c in aristas:
            agg[(u,v)] = agg.get((u,v), 0.0) + c
        
        self.aristas = [(u,v,c) for (u,v),c in agg.items()]
        
        self.origen_entrada.delete(0, tk.END)
        self.origen_entrada.insert(0, self.origen)
        self.destino_entrada.delete(0, tk.END)
        self.destino_entrada.insert(0, self.destino)
        
        self.estado["text"] = f"Grafo aleatorio ordenado con {n} nodos (A...{self.destino}) cargado. Presiona Ejecutar."
        self.redibujar()

    def cargar_varios_ejemplos(self):
        self.lista_ejemplos = []
        
        for _ in range(5):
            n = random.randint(5, 7)
            
            nodos_coords, origen, destino = self._generar_layout_circular(n)
            letras = list(nodos_coords.keys())
            
            aristas = []
            
            # 1. Garantizar una ruta de A al último nodo
            for i in range(n - 1):
                u, v = letras[i], letras[i + 1]
                capacidad = random.randint(10, 30) 
                aristas.append((u, v, capacidad))
            
            # 2. Agregar aristas aleatorias adicionales
            for i in range(n):
                for j in range(n):
                    u, v = letras[i], letras[j]
                    if u != v and random.random() < 0.4:
                        if (u, v) not in [(letras[k], letras[k+1]) for k in range(n-1)]:
                            capacidad = random.randint(5, 20)
                            aristas.append((u, v, capacidad))
                            
            # Agrupar capacidades si hay aristas duplicadas
            agg = {}
            for u,v,c in aristas:
                agg[(u,v)] = agg.get((u,v), 0.0) + c
            
            unique_aristas = [(u,v,c) for (u,v),c in agg.items()]
            
            ejemplo = {"nodos": nodos_coords, "aristas": unique_aristas, "origen": origen, "destino": destino}
            self.lista_ejemplos.append(ejemplo)
            
        if self.lista_ejemplos:
            self.indice_ejemplo = 0
            self._cargar_ejemplo_desde_lista()
            self.estado["text"] = f"Ejemplo 1 de {len(self.lista_ejemplos)} cargado. Presiona Ejecutar."
        else:
             self.estado["text"] = "No se pudieron generar ejemplos."

    def _cargar_ejemplo_desde_lista(self):
        self.ultimo_flujo = None
        if not self.lista_ejemplos: return
        
        ejemplo = self.lista_ejemplos[self.indice_ejemplo]
        self.nodos = ejemplo["nodos"]
        self.aristas = ejemplo["aristas"]
        self.origen = ejemplo["origen"]
        self.destino = ejemplo["destino"]
        
        self.origen_entrada.delete(0, tk.END)
        if self.origen: self.origen_entrada.insert(0, self.origen)
        self.destino_entrada.delete(0, tk.END)
        if self.destino: self.destino_entrada.insert(0, self.destino)
        
        self.redibujar()

    def ejemplo_anterior(self):
        if hasattr(self, "lista_ejemplos") and self.indice_ejemplo > 0:
            self.indice_ejemplo -= 1
            self._cargar_ejemplo_desde_lista()
            self.estado["text"] = f"Ejemplo {self.indice_ejemplo+1} de {len(self.lista_ejemplos)} cargado."

    def ejemplo_siguiente(self):
        if hasattr(self, "lista_ejemplos") and self.indice_ejemplo < len(self.lista_ejemplos)-1:
            self.indice_ejemplo += 1
            self._cargar_ejemplo_desde_lista()
            self.estado["text"] = f"Ejemplo {self.indice_ejemplo+1} de {len(self.lista_ejemplos)} cargado."

    def cargar_ejemplo(self):
        self.limpiar_todo(confirmar=False)
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        
        center_x = max(200, w / 2)
        center_y = max(200, h / 2)
        
        # Posiciones que replican el layout de la imagen del CLRS
        self.nodos["A"] = {"x": center_x - 200, "y": center_y}
        self.nodos["B"] = {"x": center_x - 100, "y": center_y - 120}
        self.nodos["C"] = {"x": center_x - 100, "y": center_y + 120}
        self.nodos["D"] = {"x": center_x + 100, "y": center_y - 120}
        self.nodos["E"] = {"x": center_x + 100, "y": center_y + 120}
        self.nodos["F"] = {"x": center_x + 200, "y": center_y}

        self.origen, self.destino = "A", "F" # A=s, F=t
        
        # Aristas que replican el ejemplo de la imagen (aunque con un par de cambios para mostrar bidireccionalidad)
        ejemplo = [
            ("A","B",16),("A","C",13),
            ("B","D",12),
            ("C","B",10), # Arista C->B (10)
            ("B","C",4), # Arista B->C (4), para mostrar desplazamiento
            
            ("C","E",14),
            ("D","F",20),
            ("E","D",7),
            ("E","F",4),
            ("C","D",9), # Arista C->D (9)
        ]
        
        # Agrupar capacidades si hay aristas duplicadas
        agg = {}
        for u,v,c in ejemplo:
            agg[(u,v)] = agg.get((u,v), 0.0) + c
        
        self.aristas = [(u,v,c) for (u,v),c in agg.items()]
        
        self.origen_entrada.delete(0, tk.END)
        self.origen_entrada.insert(0, self.origen)
        self.destino_entrada.delete(0, tk.END)
        self.destino_entrada.insert(0, self.destino)
        
        self.estado["text"] = "Ejemplo clásico (CLRS) con estilo moderno cargado. Presiona Ejecutar."
        self.redibujar()


    def guardar_json(self):
        aristas_serializables = [[u, v, c] for u, v, c in self.aristas]
        datos = {"nodos": self.nodos, "aristas": aristas_serializables, "origen": self.origen, "destino": self.destino}
        
        ruta = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON","*.json")])
        if ruta:
            try:
                with open(ruta, "w", encoding="utf-8") as f:
                    json.dump(datos, f, indent=2)
                self.estado["text"] = f"Grafo guardado en {ruta.split('/')[-1]}."
            except Exception as e:
                messagebox.showerror("Error de Guardado", f"No se pudo guardar el archivo: {e}")

    def cargar_json(self):
        ruta = filedialog.askopenfilename(filetypes=[("JSON","*.json")])
        if ruta:
            try:
                with open(ruta, "r", encoding="utf-8") as f:
                    datos = json.load(f)
                    
                self.nodos = datos.get("nodos", {})
                # Asegurar que la capacidad se carga como float
                self.aristas = [(u,v,float(c)) for u,v,c in datos.get("aristas", [])]
                self.origen, self.destino = datos.get("origen"), datos.get("destino")
                self.ultimo_flujo = None
                
                self.origen_entrada.delete(0, tk.END)
                if self.origen: self.origen_entrada.insert(0, self.origen)
                self.destino_entrada.delete(0, tk.END)
                if self.destino: self.destino_entrada.insert(0, self.destino)
                
                self.estado["text"] = f"Grafo cargado desde {ruta.split('/')[-1]}."
                self.redibujar()
            except Exception as e:
                 messagebox.showerror("Error de Carga", f"No se pudo cargar el archivo o el formato es incorrecto: {e}")

    def limpiar_todo(self, confirmar=True):
        if confirmar and not messagebox.askyesno("Confirmar", "¿Limpiar todo el grafo (nodos, aristas y flujo)?"):
            return
        self.nodos.clear()
        self.aristas.clear()
        self.origen, self.destino = None, None
        self.ultimo_flujo = None
        self.lista_ejemplos = []
        self.indice_ejemplo = -1
        
        self.origen_entrada.delete(0, tk.END)
        self.destino_entrada.delete(0, tk.END)
        
        self.estado["text"] = "Grafo limpio. Comience a agregar nodos."
        self.redibujar()

    # --- Interacción de Arrastre ---
    def _on_click(self, e):
        for nid, pos in self.nodos.items():
            if (pos["x"]-e.x)**2 + (pos["y"]-e.y)**2 <= RADIO_NODO**2:
                self.arrastrando, self.desfase = nid, (pos["x"]-e.x, pos["y"]-e.y)
                return
        self.arrastrando = None

    def _on_drag(self, e):
        if self.arrastrando:
            self.nodos[self.arrastrando]["x"] = e.x + self.desfase[0]
            self.nodos[self.arrastrando]["y"] = e.y + self.desfase[1]
            w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
            self.nodos[self.arrastrando]["x"] = max(RADIO_NODO, min(w - RADIO_NODO, self.nodos[self.arrastrando]["x"]))
            self.nodos[self.arrastrando]["y"] = max(RADIO_NODO, min(h - RADIO_NODO, self.nodos[self.arrastrando]["y"]))
            self.redibujar()

    def _on_release(self, e):
        self.arrastrando = None
    # -------------------------------

    def redibujar(self):
        self.canvas.delete("all")
        self._dibujar_cuadricula()
        
        # Dibujar aristas (líneas y capacidad)
        for (u,v,cap) in self._aristas_agrupadas():
            self._dibujar_arista_linea(u,v,cap)
            
        # Dibujar flujo y capacidad sobre las aristas
        if self.ultimo_flujo:
            for (u,v), f in self.ultimo_flujo["pares"].items():
                cap = self.ultimo_flujo["capacidad"].get((u,v), 0.0)
                if cap > 0:
                    self._dibujar_flujo_texto(u,v,f,cap)
                    
        # Dibujar nodos
        for nid in self.nodos:
            color = COLORES["nodo"]
            if nid == self.origen: color = COLORES["nodo_origen"]
            elif nid == self.destino: color = COLORES["nodo_destino"]
            self._dibujar_nodo(nid,color)

    def _dibujar_cuadricula(self):
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        for x in range(0, w, 40):
            self.canvas.create_line(x, 0, x, h, fill=COLORES["cuadricula"], tags="grid")
        for y in range(0, h, 40):
            self.canvas.create_line(0, y, w, y, fill=COLORES["cuadricula"], tags="grid")

    def _dibujar_nodo(self, nid, color):
        x, y = self.nodos[nid]["x"], self.nodos[nid]["y"]
        self.canvas.create_oval(x-RADIO_NODO, y-RADIO_NODO, x+RADIO_NODO, y+RADIO_NODO, fill=color, outline="", tags=nid)
        self.canvas.create_text(x, y, text=str(nid), fill=COLORES["texto"], font=("Arial", 11, "bold"), tags=nid)

    def _aristas_agrupadas(self):
        # Agrupa aristas por (u, v) y suma sus capacidades
        agg = {}
        for u,v,c in self.aristas:
            agg[(u,v)] = agg.get((u,v),0.0)+float(c)
        return [(u,v,c) for (u,v),c in agg.items()]

    def _dibujar_arista_linea(self, u,v,cap):
        if u not in self.nodos or v not in self.nodos: return
        
        # Verificar si existe la arista opuesta (v -> u)
        existe_opuesta = any(a[0] == v and a[1] == u for a in self.aristas)
        
        # Determinar el desplazamiento: 0 si es unidireccional, ESPACIO_ARISTA si es bidireccional
        desplazamiento = ESPACIO_ARISTA / 2 if existe_opuesta else 0

        x1,y1=self.nodos[u]["x"],self.nodos[u]["y"]
        x2,y2=self.nodos[v]["x"],self.nodos[v]["y"]
        dx,dy=x2-x1,y2-y1; dist=math.hypot(dx,dy) or 1
        
        # Vector unitario y normal (perpendicular)
        ux,uy=dx/dist,dy/dist 
        nx,ny=-uy,ux
        
        # Aplicar desplazamiento perpendicular para separar aristas bidireccionales
        x1_disp, y1_disp = x1 + nx * desplazamiento, y1 + ny * desplazamiento
        x2_disp, y2_disp = x2 + nx * desplazamiento, y2 + ny * desplazamiento

        # Ajustar los puntos de inicio y fin para que no toquen el centro del nodo
        offset = RADIO_NODO + 2
        x1_adj, y1_adj = x1_disp + ux * offset, y1_disp + uy * offset
        x2_adj, y2_adj = x2_disp - ux * offset, y2_disp - uy * offset
        
        # Dibujar la línea de la arista
        color=COLORES["arista"]; ancho=2
        flujo_actual = self.ultimo_flujo["pares"].get((u,v), 0.0) if self.ultimo_flujo else 0.0
        
        # Resaltar si la arista está saturada
        if cap > 0 and abs(flujo_actual - cap) < 1e-9: 
            color=COLORES["arista_sat"]; ancho=3
            
        self.canvas.create_line(x1_adj, y1_adj, x2_adj, y2_adj, fill=color, width=ancho, 
                                arrow=tk.LAST, arrowshape=(TAM_FLECHA, TAM_FLECHA, TAM_FLECHA/2), tags=f"arista_{u}_{v}")
        
        # Posición para el texto de capacidad
        mx,my=(x1_adj+x2_adj)/2,(y1_adj+y2_adj)/2
        
        # Desplazamiento del texto paralelo a la línea (lejos del centro)
        perp_dx, perp_dy = -uy, ux # Vector perpendicular (normal) al vector de arista
        
        # Desplazar texto de capacidad aún más lejos para evitar superposición con el flujo
        cap_offset = 20 if existe_opuesta else 10 
        cap_x, cap_y = mx + nx * cap_offset, my + ny * cap_offset 
        
        self.canvas.create_text(cap_x, cap_y, text=str(int(cap)), fill=COLORES["texto"], font=("Arial",10, "bold"), tags=f"cap_text_{u}_{v}")

    def _dibujar_flujo_texto(self,u,v,f,c):
        if u not in self.nodos or v not in self.nodos: return
        
        # Verificar si existe la arista opuesta (v -> u)
        existe_opuesta = any(a[0] == v and a[1] == u for a in self.aristas)

        # Determinar el desplazamiento de la arista
        desplazamiento = ESPACIO_ARISTA / 2 if existe_opuesta else 0

        x1,y1=self.nodos[u]["x"],self.nodos[u]["y"]
        x2,y2=self.nodos[v]["x"],self.nodos[v]["y"]
        dx,dy=x2-x1,y2-y1; dist=math.hypot(dx,dy) or 1
        
        # Vector unitario y normal (perpendicular)
        ux,uy=dx/dist,dy/dist
        nx,ny=-uy,ux
        
        # Aplicar desplazamiento perpendicular de la línea
        x1_disp, y1_disp = x1 + nx * desplazamiento, y1 + ny * desplazamiento
        x2_disp, y2_disp = x2 + nx * desplazamiento, y2 + ny * desplazamiento
        
        # Ajustar los puntos de inicio y fin para que no toquen el centro del nodo
        offset = RADIO_NODO + 2
        x1_adj, y1_adj = x1_disp + ux * offset, y1_disp + uy * offset
        x2_adj, y2_adj = x2_disp - ux * offset, y2_disp - uy * offset
        mx,my=(x1_adj+x2_adj)/2,(y1_adj+y2_adj)/2
        
        # Desplazamiento del texto de flujo, opuesto a la capacidad
        flujo_offset = 20 if existe_opuesta else 10 # Desplazar lo suficiente
        
        px,py = mx - nx * flujo_offset, my - ny * flujo_offset # Mover en la dirección opuesta al texto de capacidad
        
        etiqueta=f"{int(f)}"
        self.canvas.create_text(px,py,text=etiqueta,fill=COLORES["arista_flujo_texto"],font=("Arial",11,"bold"), 
                                tags=f"flow_text_{u}_{v}", 
                                anchor="center", 
                                justify="center",
                                )

# ---------- main ----------
if __name__=="__main__":
    raiz=tk.Tk()
    app=FlujoMaximoGUI(raiz)
    raiz.mainloop()
