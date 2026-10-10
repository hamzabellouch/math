import OAI.Combinatorics.PolynomialVacuum.Cylinder.FiniteArcs
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StripArcs

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

def translate (x : ZMod M) (y : ℤ) : Vertex M → Vertex M
  | .up i j => .up (i+x) (j+y)
  | .down i j => .down (i+x) (j+y)
def rotate (H : ℤ) : Vertex M → Vertex M
  | .up i j => .down (-i) (H-1-j)
  | .down i j => .up (-i) (H-1-j)
def mapGerm (f : Vertex M → Vertex M) (g : Germ M) : Germ M := (f g.1,g.2)

@[simp] theorem translate_neighbor_cyl (x : ZMod M) (y : ℤ) (v : Vertex M) (k : Fin 3) :
    translate x y (neighbor v k)=neighbor (translate x y v) k := by
  cases v <;> fin_cases k <;> simp [translate,neighbor] <;> ring
@[simp] theorem rotate_neighbor (H : ℤ) (v : Vertex M) (k : Fin 3) :
    rotate H (neighbor v k)=neighbor (rotate H v) k := by
  cases v <;> fin_cases k <;> simp [rotate,neighbor] <;> ring
@[simp] theorem rotate_invol (H : ℤ) (v : Vertex M) : rotate H (rotate H v)=v := by
  cases v <;> simp [rotate]
@[simp] theorem translate_comp (x a : ZMod M) (y b : ℤ) (v : Vertex M) :
    translate x y (translate a b v)=translate (a+x) (b+y) v := by
  cases v <;> simp [translate,add_assoc]
@[simp] theorem translate_zero (v : Vertex M) : translate 0 0 v=v := by cases v <;> simp [translate]

theorem translate_injective (x : ZMod M) (y : ℤ) : Function.Injective (translate x y) := by
  intro v w h
  have he:=congrArg (translate (-x) (-y)) h
  simpa using he

theorem map_advance (f : Vertex M → Vertex M) (hf : ∀v k,f (neighbor v k)=neighbor (f v) k)
    (g : Germ M) (b : Bool) : mapGerm f (advance g b)=advance (mapGerm f g) b := by
  simp [mapGerm,advance,outgoingSlot,hf]
theorem map_terminal (f : Vertex M → Vertex M) (hf : ∀v k,f (neighbor v k)=neighbor (f v) k)
    (g : Germ M) (w : List Bool) : mapGerm f (terminalGerm g w)=terminalGerm (mapGerm f g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [terminalGerm,← map_advance f hf,ih]
theorem map_traced (f : Vertex M → Vertex M) (hf : ∀v k,f (neighbor v k)=neighbor (f v) k)
    (g : Germ M) (w : List Bool) : (traced g w).map f=traced (mapGerm f g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [traced,List.map_cons,← map_advance f hf,← ih]; rfl
@[simp] theorem translate_layer (x : ZMod M) (y : ℤ) (v : Vertex M) :
    vertexLayer (translate x y v)=vertexLayer v+y := by cases v <;> rfl
@[simp] theorem rotate_layer (H : ℤ) (v : Vertex M) :
    vertexLayer (rotate H v)=H-1-vertexLayer v := by cases v <;> rfl

theorem rotate_band (H : ℕ) (v : Vertex M) : InBand H (rotate H v) ↔ InBand H v := by
  simp only [InBand,rotate_layer]
  omega

theorem translate_band (x : ZMod M) (H : ℕ) (v : Vertex M) :
    InBand H (translate x 0 v) ↔ InBand H v := by simp [InBand]
end PolynomialVacuumCylinder

end OAI
