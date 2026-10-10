import Mathlib.Data.Fintype.Powerset
import OAI.Combinatorics.BalancedRyser.Local.ReuseOrdering

namespace OAI

namespace Balanced
open scoped _root_.Balanced

def fixedGeneratorPositions (old : Finset (Fin 4)) : Finset (Fin 4) :=
  old.filter (fun i => i + 1 ∈ old)

theorem fixedGeneratorPositions_table : ∀ old : Finset (Fin 4),
    (old.card = 0 → (fixedGeneratorPositions old).card = 0) ∧
    (old.card = 1 → (fixedGeneratorPositions old).card = 0) ∧
    (old.card = 2 → (fixedGeneratorPositions old).card ≤ 1) ∧
    (old.card = 3 → (fixedGeneratorPositions old).card ≤ 2) ∧
    (old.card = 4 → (fixedGeneratorPositions old).card = 4) := by
  decide

def reuseCountingExponent (old : Finset (Fin 4)) : ℕ :=
  if (fixedGeneratorPositions old).card = 0 then old.card
  else old.card + 1 - (fixedGeneratorPositions old).card

theorem reuseSaving_le_countingExponent : ∀ old : Finset (Fin 4),
    reuseSaving old.card ≤ reuseCountingExponent old := by
  decide

theorem reuseSaving_table :
    reuseSaving 0 = 0 ∧ reuseSaving 1 = 1 ∧ reuseSaving 2 = 2 ∧
    reuseSaving 3 = 2 ∧ reuseSaving 4 = 1 := by
  decide

end Balanced

end OAI
