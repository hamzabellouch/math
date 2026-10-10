import OAI.Combinatorics.EditApproximation.Coarse.CoarseEntryCostSum
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseInputWork

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

/-- Bit arithmetic is executed once for each fresh coarse source request. -/
noncomputable def physicalFamilyCoarseBitWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) : ℝ :=
  let initial := clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse)
  let result := chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  coarseEntryCostSum source target N depth coarse
    (fun entry => Sum.inr (Sum.inl entry) ∈ result.freshKeys)

theorem physicalFamilyCoarseBitWork_bound (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) (C : ℝ)
    (hc : ∀ entry : PhysicalEntry M J target.length,
      (coarseEntryBinaryCost N B (depth entry) (physicalSource source entry.1)
        (substring target entry.2.lo entry.2.hi) (coarse entry) : ℝ) ≤
        C * ((coarseInitialArrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
          (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (coarse entry) : ℝ) +
          ((physicalSource source entry.1).length + 1 : ℕ))) :
    physicalFamilyCoarseBitWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw depth bits encode root coarse ≤ C *
      (physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta draw B depth bits encode root coarse +
       physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta
        (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        draw bits encode root) := by
  unfold physicalFamilyCoarseBitWork physicalFamilyMemoCoarseWork physicalFamilyCoarseInputWork
  exact coarseEntryCostSum_bound source target N depth coarse _ C hc

end Coarse
end EditApproximation

end OAI
