import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute

namespace OAI

/-! Square-lattice placements for the even and odd singlet subdivision gadgets. -/

namespace ContinuumCoulomb
open scoped Classical

def qmaPathPatchVertex (even : Bool) : Fin 4 → ℕ × ℕ :=
  if even then ![(0,0),(2,0),(1,0),(1,1)] else ![(0,0),(3,0),(1,0),(2,0)]
def qmaPathPatchLeft : Fin 3 → Fin 4 := ![2,0,1]
def qmaPathPatchRight (even : Bool) : Fin 3 → Fin 4 := ![3,2,if even then 2 else 3]

theorem qmaPathPatch_vertices (even : Bool) : Function.Injective (qmaPathPatchVertex even) := by
  cases even <;> decide

theorem qmaPathPatch_adjacent (even : Bool) (e : Fin 3) :
    Nat.dist (qmaPathPatchVertex even (qmaPathPatchLeft e)).1
      (qmaPathPatchVertex even (qmaPathPatchRight even e)).1+
    Nat.dist (qmaPathPatchVertex even (qmaPathPatchLeft e)).2
      (qmaPathPatchVertex even (qmaPathPatchRight even e)).2 = 1 := by
  cases even <;> fin_cases e <;> decide

theorem qmaPathPatch_degree (even : Bool) (v : Fin 4) :
    (Finset.univ.filter (fun e => qmaPathPatchLeft e = v ∨ qmaPathPatchRight even e = v)).card ≤ 3 := by
  cases even <;> fin_cases v <;> decide

end ContinuumCoulomb

end OAI
