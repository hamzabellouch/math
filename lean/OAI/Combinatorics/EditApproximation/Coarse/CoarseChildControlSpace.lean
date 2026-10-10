import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedChildren

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Invocation count follows the same child sequence, thresholds, recursive calls,
penalty sweeps and accumulated array as the indexed evaluator. -/
def coarseIndexChildrenInvocations {B : ℕ} (q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ)
    (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (allocation : Fin B → BinaryFraction → ℕ → ℕ)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) : List (Fin B) → ℕ → ℕ
  | [], _ => 1
  | i :: rest, start =>
    let threshold := coarseChildThresholdWithWork B q allowance (draw i)
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate i childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseIndexChildren 0 q L two width evaluate draw allowance rest (start + width i)
    coarseChildThresholdInvocations B q allowance (draw i) +
      coarseChildAllowanceInvocations L threshold.1 + allocation i childAllowance.1 start +
      coarseBinaryPenaltyInvocations two evaluated.1 + coarseChildAllowanceInvocations q allowance +
      coarseBinaryMapInvocations (coarseContributionInvocations threshold.1 scale.1) penalty.1 +
      coarseIndexChildrenInvocations q L two width evaluate allocation draw allowance rest (start + width i) +
      coarseBinaryAddInvocations contribution.1 remainder.1 + 1

/-- The loop's first argument does not contribute to its runtime control space. -/
private theorem coarseIndexChildren_unused_k {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexChildren k q L two width evaluate draw allowance indices start =
      coarseIndexChildren 0 q L two width evaluate draw allowance indices start := by
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexChildren, ih]

theorem coarseIndexChildrenInvocations_le_work {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ)
    (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (allocation : Fin B → BinaryFraction → ℕ → ℕ)
    (hallocation : ∀ i a start, allocation i a start ≤ 2 * (evaluate i a start).2 + 1)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexChildrenInvocations q L two width evaluate allocation draw allowance indices start ≤
      2 * (coarseIndexChildren k q L two width evaluate draw allowance indices start).2 + 1 := by
  rw [coarseIndexChildren_unused_k]
  induction indices generalizing start with
  | nil => exact Nat.le_refl 1
  | cons i rest ih =>
    let threshold := coarseChildThresholdWithWork B q allowance (draw i)
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate i childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseIndexChildren 0 q L two width evaluate draw allowance rest (start + width i)
    have ht := coarseChildThresholdInvocations_le_work B q allowance (draw i)
    have ha := coarseChildAllowanceInvocations_le_work L threshold.1
    have he := hallocation i childAllowance.1 start
    have hp := coarseBinaryPenaltyInvocations_le_work two evaluated.1
    have hs := coarseChildAllowanceInvocations_le_work q allowance
    have hm := coarseBinaryMapInvocations_le_work
      (coarseContributionWithWork threshold.1 scale.1)
      (coarseContributionInvocations threshold.1 scale.1)
      (coarseContributionInvocations_le_work threshold.1 scale.1) penalty.1
    have hr := ih (start + width i)
    have had := coarseBinaryAddInvocations_le_work contribution.1 remainder.1
    change coarseChildThresholdInvocations B q allowance (draw i) +
      coarseChildAllowanceInvocations L threshold.1 + allocation i childAllowance.1 start +
      coarseBinaryPenaltyInvocations two evaluated.1 + coarseChildAllowanceInvocations q allowance +
      coarseBinaryMapInvocations (coarseContributionInvocations threshold.1 scale.1) penalty.1 +
      coarseIndexChildrenInvocations q L two width evaluate allocation draw allowance rest (start + width i) +
      coarseBinaryAddInvocations contribution.1 remainder.1 + 1 ≤
      2 * (threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
        remainder.2 + (coarseBinaryAddWithWork contribution.1 remainder.1).2 +
        Nat.size start + Nat.size (width i) + 9) + 1
    change coarseChildThresholdInvocations B q allowance (draw i) ≤ threshold.2 at ht
    change coarseChildAllowanceInvocations L threshold.1 ≤ childAllowance.2 at ha
    change allocation i childAllowance.1 start ≤ 2 * evaluated.2 + 1 at he
    change coarseBinaryPenaltyInvocations two evaluated.1 ≤ 2 * penalty.2 + 9 at hp
    change coarseChildAllowanceInvocations q allowance ≤ scale.2 at hs
    change coarseBinaryMapInvocations (coarseContributionInvocations threshold.1 scale.1) penalty.1 ≤
      contribution.2 + 2 at hm
    change coarseIndexChildrenInvocations q L two width evaluate allocation draw allowance rest (start + width i) ≤
      2 * remainder.2 + 1 at hr
    omega

end BinaryFraction
end EditApproximation

end OAI
