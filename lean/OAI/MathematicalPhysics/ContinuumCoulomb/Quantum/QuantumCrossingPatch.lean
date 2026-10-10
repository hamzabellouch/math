import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingGraph

namespace OAI

/-! A concrete square-grid subdivision of the nine-edge crossing gadget.
Its four terminals lie on the boundary with their outward directions free. -/

namespace ContinuumCoulomb
open scoped Classical

def qmaCrossingPatchVertex : Fin 6 → ℕ × ℕ := ![(0,6),(6,12),(12,6),(6,0),(4,8),(8,4)]
def qmaCrossingPatchLeft : Fin 9 → Fin 6 := ![4,0,1,2,3,0,1,2,3]
def qmaCrossingPatchRight : Fin 9 → Fin 6 := ![5,4,4,5,5,1,2,3,0]
def qmaCrossingPatchPath : Fin 9 → List (ℕ × ℕ) := ![
  [(4,8),(5,8),(6,8),(7,8),(8,8),(8,7),(8,6),(8,5),(8,4)],
  [(0,6),(1,6),(2,6),(2,7),(2,8),(3,8),(4,8)],
  [(6,12),(6,11),(6,10),(5,10),(4,10),(4,9),(4,8)],
  [(12,6),(11,6),(10,6),(10,5),(10,4),(9,4),(8,4)],
  [(6,0),(6,1),(6,2),(7,2),(8,2),(8,3),(8,4)],
  [(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(1,12),(2,12),(3,12),(4,12),(5,12),(6,12)],
  [(6,12),(7,12),(8,12),(9,12),(10,12),(11,12),(12,12),(12,11),(12,10),(12,9),(12,8),(12,7),(12,6)],
  [(12,6),(12,5),(12,4),(12,3),(12,2),(12,1),(12,0),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0)],
  [(6,0),(5,0),(4,0),(3,0),(2,0),(1,0),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]]

theorem qmaCrossingPatch_endpoints (e : Fin 9) :
    (qmaCrossingPatchPath e).head? = some (qmaCrossingPatchVertex (qmaCrossingPatchLeft e)) ∧
    (qmaCrossingPatchPath e).getLast? = some (qmaCrossingPatchVertex (qmaCrossingPatchRight e)) := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_chain (e : Fin 9) :
    (qmaCrossingPatchPath e).IsChain
      (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_simple (e : Fin 9) : (qmaCrossingPatchPath e).Nodup := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_bounded (e : Fin 9) :
    ∀ p ∈ qmaCrossingPatchPath e, p.1 ≤ 12 ∧ p.2 ≤ 12 := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_length (e : Fin 9) : (qmaCrossingPatchPath e).length ≤ 13 := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_disjoint (e f : Fin 9) (hef : e ≠ f) :
    Disjoint ((qmaCrossingPatchPath e).drop 1 |>.dropLast).toFinset
      (qmaCrossingPatchPath f).toFinset := by
  fin_cases e <;> fin_cases f <;> first | exact (hef rfl).elim | decide

theorem qmaCrossingPatch_vertices : Function.Injective qmaCrossingPatchVertex := by decide

def qmaCrossingPatchInt (p : ℕ × ℕ) : ℤ × ℤ := (p.1,p.2)
def qmaCrossingPatchPort : Fin 4 → ℤ × ℤ := ![(-1,6),(6,13),(13,6),(6,-1)]

theorem qmaCrossingPatch_port_step (a : Fin 4) :
    Int.natAbs ((qmaCrossingPatchPort a).1-
      (qmaCrossingPatchInt (qmaCrossingPatchVertex (a.castLE (by decide)))).1)+
    Int.natAbs ((qmaCrossingPatchPort a).2-
      (qmaCrossingPatchInt (qmaCrossingPatchVertex (a.castLE (by decide)))).2) = 1 := by
  fin_cases a <;> decide

theorem qmaCrossingPatch_port_unused (a : Fin 4) (e : Fin 9) :
    qmaCrossingPatchPort a ∉ (qmaCrossingPatchPath e).map qmaCrossingPatchInt := by
  fin_cases a <;> fin_cases e <;> decide

theorem qmaCrossingPatch_interior_fresh (e : Fin 9) :
    Disjoint ((qmaCrossingPatchPath e).drop 1 |>.dropLast).toFinset
      (Finset.univ.image qmaCrossingPatchVertex) := by
  fin_cases e <;> decide

end ContinuumCoulomb

end OAI
