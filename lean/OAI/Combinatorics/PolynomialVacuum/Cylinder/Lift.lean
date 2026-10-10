import OAI.Combinatorics.PolynomialVacuum.Cylinder.Contour
import OAI.Combinatorics.HoneycombCorridor.BoundaryArcs

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}
abbrev PlaneVertex := PolynomialVacuumBridge.Corridor.Vertex
abbrev PlaneGerm := PolynomialVacuumBridge.Corridor.Germ

def projectVertex (M : ℕ) : PlaneVertex → Vertex M
  | .up i j => .up (i : ZMod M) j
  | .down i j => .down (i : ZMod M) j

def projectGerm (M : ℕ) (g : PlaneGerm) : Germ M := (projectVertex M g.1,g.2)

def translateVertex (d : ℤ) : PlaneVertex → PlaneVertex
  | .up i j => .up (i+d) j
  | .down i j => .down (i+d) j

def translateGerm (d : ℤ) (g : PlaneGerm) : PlaneGerm := (translateVertex d g.1,g.2)

@[simp] theorem translateVertex_zero (v : PlaneVertex) : translateVertex 0 v=v := by cases v <;> simp [translateVertex]
@[simp] theorem translateGerm_zero (g : PlaneGerm) : translateGerm 0 g=g := by simp [translateGerm]
@[simp] theorem translateVertex_add (d e : ℤ) (v : PlaneVertex) :
    translateVertex d (translateVertex e v)=translateVertex (d+e) v := by
  cases v <;> simp [translateVertex] <;> ring
@[simp] theorem translateGerm_add (d e : ℤ) (g : PlaneGerm) :
    translateGerm d (translateGerm e g)=translateGerm (d+e) g := by
  simp [translateGerm]

theorem translateVertex_injective (d : ℤ) : Function.Injective (translateVertex d) := by
  intro v u h
  have := congrArg (translateVertex (-d)) h
  simpa using this

theorem translateVertex_cancel (d e : ℤ) (v : PlaneVertex) :
    translateVertex d v=translateVertex e v ↔ d=e := by
  cases v <;> simp [translateVertex]

@[simp] theorem project_neighbor (v : PlaneVertex) (k : Fin 3) :
    projectVertex M (PolynomialVacuumBridge.Corridor.neighbor v k)=neighbor (projectVertex M v) k := by
  cases v <;> fin_cases k <;> simp [projectVertex,PolynomialVacuumBridge.Corridor.neighbor,neighbor]
@[simp] theorem project_advance (g : PlaneGerm) (b : Bool) :
    projectGerm M (PolynomialVacuumBridge.Corridor.advance g b)=advance (projectGerm M g) b := by
  simp [projectGerm,PolynomialVacuumBridge.Corridor.advance,advance,PolynomialVacuumBridge.Corridor.outgoingSlot,outgoingSlot]
@[simp] theorem project_terminal (g : PlaneGerm) (w : List Bool) :
    projectGerm M (PolynomialVacuumBridge.Corridor.terminalGerm g w)=terminalGerm (projectGerm M g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [PolynomialVacuumBridge.Corridor.terminalGerm,terminalGerm,ih,project_advance]
@[simp] theorem project_traced (g : PlaneGerm) (w : List Bool) :
    (PolynomialVacuumBridge.Corridor.traced g w).map (projectVertex M)=traced (projectGerm M g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [PolynomialVacuumBridge.Corridor.traced,traced,List.map_cons,ih,project_advance]; rfl

@[simp] theorem translate_neighbor (d : ℤ) (v : PlaneVertex) (k : Fin 3) :
    translateVertex d (PolynomialVacuumBridge.Corridor.neighbor v k)=PolynomialVacuumBridge.Corridor.neighbor (translateVertex d v) k := by
  cases v <;> fin_cases k <;> simp [translateVertex,PolynomialVacuumBridge.Corridor.neighbor] <;> omega
@[simp] theorem translate_advance (d : ℤ) (g : PlaneGerm) (b : Bool) :
    translateGerm d (PolynomialVacuumBridge.Corridor.advance g b)=PolynomialVacuumBridge.Corridor.advance (translateGerm d g) b := by
  simp [translateGerm,PolynomialVacuumBridge.Corridor.advance,PolynomialVacuumBridge.Corridor.outgoingSlot]
@[simp] theorem translate_terminal (d : ℤ) (g : PlaneGerm) (w : List Bool) :
    translateGerm d (PolynomialVacuumBridge.Corridor.terminalGerm g w)=PolynomialVacuumBridge.Corridor.terminalGerm (translateGerm d g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [PolynomialVacuumBridge.Corridor.terminalGerm,← ih,← translate_advance]
@[simp] theorem translate_traced (d : ℤ) (g : PlaneGerm) (w : List Bool) :
    (PolynomialVacuumBridge.Corridor.traced g w).map (translateVertex d)=PolynomialVacuumBridge.Corridor.traced (translateGerm d g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [PolynomialVacuumBridge.Corridor.traced,List.map_cons,ih,← translate_advance]; rfl

theorem closure_is_translate (g : PlaneGerm) (w : List Bool)
    (hc : terminalGerm (projectGerm M g) w=projectGerm M g) :
    ∃ d : ℤ, (d : ZMod M)=0 ∧ PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g := by
  rw [← project_terminal] at hc
  let t := PolynomialVacuumBridge.Corridor.terminalGerm g w
  change projectGerm M t=projectGerm M g at hc
  change ∃ d : ℤ, (d : ZMod M)=0 ∧ t=translateGerm d g
  rcases g with ⟨v,k⟩
  rcases t with ⟨u,l⟩
  cases v <;> cases u <;> simp only [projectGerm,projectVertex,Prod.mk.injEq,Vertex.up.injEq,Vertex.down.injEq] at hc
  · rename_i i j x y
    refine ⟨x-i,?_,?_⟩
    · simp [hc.1.1]
    · simp [translateGerm,translateVertex,hc.1.2,hc.2]
  · cases hc.1
  · cases hc.1
  · rename_i i j x y
    refine ⟨x-i,?_,?_⟩
    · simp [hc.1.1]
    · simp [translateGerm,translateVertex,hc.1.2,hc.2]

@[simp] theorem project_translate (d : ℤ) (hd : (d : ZMod M)=0) (v : PlaneVertex) :
    projectVertex M (translateVertex d v)=projectVertex M v := by
  cases v <;> simp [translateVertex,projectVertex,hd]

end PolynomialVacuumCylinder

end OAI
