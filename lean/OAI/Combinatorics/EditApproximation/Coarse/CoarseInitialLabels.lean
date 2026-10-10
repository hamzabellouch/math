import OAI.Combinatorics.EditApproximation.Coarse.CoarseLabelWork
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Only labels in roots actually reached by the dyadic initializer are drawn. -/


theorem coarseInitialLabelCount_le_arrayWork {α : Type*} [DecidableEq α]
    (B d : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    coarseInitialLabelCount B d Q lam x y draws ≤ coarseInitialArrayWork B d Q lam x y draws := by
  unfold coarseInitialLabelCount coarseInitialArrayWork
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact Finset.sum_le_sum (fun i _ => coarseLabelCount_le_arrayWork
      (coarseGuess (coarseEntryWidth x y) i) Q lam (coarseEntryTree B d x y) (draws i) _)

def coarseInitialSamplingBits {α : Type*} [DecidableEq α]
    (r d : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws (2 ^ r) d) : ℕ :=
  r * coarseInitialLabelCount (2 ^ r) d Q lam x y draws

theorem coarseInitialSamplingBits_le {α : Type*} [DecidableEq α]
    (r d : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws (2 ^ r) d) :
    coarseInitialSamplingBits r d Q lam x y draws ≤
      r * coarseInitialArrayWork (2 ^ r) d Q lam x y draws :=
  Nat.mul_le_mul_left r (coarseInitialLabelCount_le_arrayWork (2 ^ r) d Q lam x y draws)

end EditApproximation

end OAI
