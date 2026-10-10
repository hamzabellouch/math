import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkSpectrum

namespace OAI

/-! A concrete planar lattice subdivision of the rational fork gadget. -/

namespace ContinuumCoulomb
open scoped Classical

def qmaForkPatchVertex : Fin 5 → ℕ × ℕ := ![(0,6),(8,12),(8,0),(3,6),(6,6)]
def qmaForkPatchLeft : Fin 5 → Fin 5 := ![3,0,1,2,1]
def qmaForkPatchRight : Fin 5 → Fin 5 := ![4,3,4,4,2]
def qmaForkPatchPath : Fin 5 → List (ℕ × ℕ) := ![
  [(3,6),(4,6),(5,6),(6,6)],
  [(0,6),(1,6),(2,6),(3,6)],
  [(8,12),(8,11),(8,10),(7,10),(6,10),(6,9),(6,8),(6,7),(6,6)],
  [(8,0),(8,1),(8,2),(7,2),(6,2),(6,3),(6,4),(6,5),(6,6)],
  [(8,12),(9,12),(10,12),(11,12),(12,12),(12,11),(12,10),(12,9),(12,8),(12,7),(12,6),(12,5),(12,4),(12,3),(12,2),(12,1),(12,0),(11,0),(10,0),(9,0),(8,0)]]

theorem qmaForkPatch_endpoints (e : Fin 5) :
    (qmaForkPatchPath e).head? = some (qmaForkPatchVertex (qmaForkPatchLeft e)) ∧
    (qmaForkPatchPath e).getLast? = some (qmaForkPatchVertex (qmaForkPatchRight e)) := by
  fin_cases e <;> decide

theorem qmaForkPatch_chain (e : Fin 5) :
    (qmaForkPatchPath e).IsChain (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases e <;> decide

theorem qmaForkPatch_simple (e : Fin 5) : (qmaForkPatchPath e).Nodup := by
  fin_cases e <;> decide

theorem qmaForkPatch_bounded (e : Fin 5) : ∀ p ∈ qmaForkPatchPath e, p.1 ≤ 12 ∧ p.2 ≤ 12 := by
  fin_cases e <;> decide

theorem qmaForkPatch_length (e : Fin 5) : (qmaForkPatchPath e).length ≤ 21 := by
  fin_cases e <;> decide

theorem qmaForkPatch_disjoint (e f : Fin 5) (hef : e ≠ f) :
    Disjoint ((qmaForkPatchPath e).drop 1 |>.dropLast).toFinset (qmaForkPatchPath f).toFinset := by
  fin_cases e <;> fin_cases f <;> first | exact (hef rfl).elim | decide

theorem qmaForkPatch_vertices : Function.Injective qmaForkPatchVertex := by decide

end ContinuumCoulomb

end OAI
