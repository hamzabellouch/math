import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedChildren

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Allocation follows the same child sequence, thresholds, recursive calls,
penalty sweeps and accumulated array as the indexed evaluator. -/
def coarseIndexChildrenAllocation {B : ℕ} (q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ)
    (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (allocation : Fin B → BinaryFraction → ℕ → ℕ)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) : List (Fin B) → ℕ → ℕ
  | [], _ => 0
  | i :: rest, start =>
    let threshold := coarseChildThresholdWithWork B q allowance (draw i)
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate i childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseIndexChildren 0 q L two width evaluate draw allowance rest (start + width i)
    coarseChildThresholdAllocation B q allowance (draw i) +
      coarseChildAllowanceAllocation L threshold.1 + allocation i childAllowance.1 start +
      coarseBinaryPenaltyAllocation two evaluated.1 + coarseChildAllowanceAllocation q allowance +
      coarseBinaryMapAllocation (coarseContributionAllocation threshold.1 scale.1) penalty.1 +
      coarseIndexChildrenAllocation q L two width evaluate allocation draw allowance rest (start + width i) +
      coarseBinaryAddAllocation contribution.1 remainder.1

/-- The loop's first argument does not contribute to its runtime allocation. -/
private theorem coarseIndexChildren_unused_k {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexChildren k q L two width evaluate draw allowance indices start =
      coarseIndexChildren 0 q L two width evaluate draw allowance indices start := by
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexChildren, ih]

theorem coarseIndexChildrenAllocation_le_work {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ)
    (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (allocation : Fin B → BinaryFraction → ℕ → ℕ)
    (hallocation : ∀ i a start, allocation i a start ≤ 2 * (evaluate i a start).2)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexChildrenAllocation q L two width evaluate allocation draw allowance indices start ≤
      2 * (coarseIndexChildren k q L two width evaluate draw allowance indices start).2 := by
  rw [coarseIndexChildren_unused_k]
  induction indices generalizing start with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
    let threshold := coarseChildThresholdWithWork B q allowance (draw i)
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate i childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseIndexChildren 0 q L two width evaluate draw allowance rest (start + width i)
    have ht := coarseChildThresholdAllocation_le_work B q allowance (draw i)
    have ha := coarseChildAllowanceAllocation_le_work L threshold.1
    have he := hallocation i childAllowance.1 start
    have hp := coarseBinaryPenaltyAllocation_le_work two evaluated.1
    have hs := coarseChildAllowanceAllocation_le_work q allowance
    have hm := coarseBinaryMapAllocation_le_work
      (coarseContributionWithWork threshold.1 scale.1)
      (coarseContributionAllocation threshold.1 scale.1)
      (coarseContributionAllocation_le_work threshold.1 scale.1) penalty.1
    have hr := ih (start + width i)
    have had := coarseBinaryAddAllocation_le_work contribution.1 remainder.1
    change coarseChildThresholdAllocation B q allowance (draw i) +
      coarseChildAllowanceAllocation L threshold.1 + allocation i childAllowance.1 start +
      coarseBinaryPenaltyAllocation two evaluated.1 + coarseChildAllowanceAllocation q allowance +
      coarseBinaryMapAllocation (coarseContributionAllocation threshold.1 scale.1) penalty.1 +
      coarseIndexChildrenAllocation q L two width evaluate allocation draw allowance rest (start + width i) +
      coarseBinaryAddAllocation contribution.1 remainder.1 ≤
      2 * (threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
        remainder.2 + (coarseBinaryAddWithWork contribution.1 remainder.1).2 +
        Nat.size start + Nat.size (width i) + 9)
    change coarseChildThresholdAllocation B q allowance (draw i) ≤ threshold.2 at ht
    change coarseChildAllowanceAllocation L threshold.1 ≤ childAllowance.2 at ha
    change allocation i childAllowance.1 start ≤ 2 * evaluated.2 at he
    change coarseBinaryPenaltyAllocation two evaluated.1 ≤ 2 * penalty.2 at hp
    change coarseChildAllowanceAllocation q allowance ≤ scale.2 at hs
    change coarseBinaryMapAllocation (coarseContributionAllocation threshold.1 scale.1) penalty.1 ≤
      contribution.2 at hm
    change coarseIndexChildrenAllocation q L two width evaluate allocation draw allowance rest (start + width i) ≤
      2 * remainder.2 at hr
    omega

end BinaryFraction
end EditApproximation

end OAI
