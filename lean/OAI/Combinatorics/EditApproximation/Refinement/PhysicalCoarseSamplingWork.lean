import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialLabels
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseInputWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

section Coarse
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

/- One binary word is consumed for every threshold label actually exposed. -/


omit [NeZero B] in
theorem physicalFamilyCoarseSamplingWork_bound (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) :
    physicalFamilyCoarseSamplingWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw depth bits encode root coarse ≤ (Nat.size B : ℝ) *
      physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta draw B depth bits encode root coarse := by
  classical
  unfold physicalFamilyCoarseSamplingWork physicalFamilyMemoCoarseWork
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro entry _
  have h := coarseInitialLabelCount_le_arrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
    (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (coarse entry)
  have hs : 0 ≤ selectionIndicator (Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
        T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger
        (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        answer bits encode root).freshKeys) := by
    unfold selectionIndicator
    split <;> norm_num
  push_cast
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (Nat.cast_nonneg (Nat.size B))) hs).trans_eq (by ring)

end Coarse
end EditApproximation

end OAI
