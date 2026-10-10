import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedValue
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialExecution
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction



theorem coarseIndexedRootWithWork_value {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    (coarseIndexedRootWithWork k q L hB hq hL x y draws).1 =
      (coarseRootWithWork k q L hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)).1 := by
  unfold coarseIndexedRootWithWork coarseRootWithWork
  dsimp only
  rw [coarseIndexedWithWork_value, coarseReadCore_eq k q L (coarseEntryWidth x y) x y
    (le_max_left _ _) (le_max_right _ _)]
  simp only [Nat.zero_add, coarseReadTree_entry]



theorem coarseIndexedCandidateWithWork_value {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    (coarseIndexedCandidateWithWork q L hB hq hL x y i draws).1 =
      (coarseCandidateWithWork q L hB hq hL x y i draws).1 := by
  simp only [coarseIndexedCandidateWithWork, coarseCandidateWithWork, coarseIndexedRootWithWork_value]

/-- The final coarse initializer executes the indexed roots and retains
only their integer-clamped minimum. -/


theorem coarseIndexedInitialWithWork_value {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    (coarseIndexedInitialWithWork q L N hB hq hL x y draws).1 =
      coarseInitialValue B d q (1 / L) N x y draws := by
  rw [← coarseInitialWithWork_value q L N hB hq hL x y draws]
  unfold coarseIndexedInitialWithWork coarseInitialWithWork
  dsimp only
  split_ifs <;> simp only [arithmeticMapWithWork_value, coarseIndexedCandidateWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
