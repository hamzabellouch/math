import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedEntryCost
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

/-- Bit arithmetic is executed once for each fresh coarse source request. -/


theorem physicalFamilyIndexedCoarseWork_bound (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) (C : ℝ)
    (hc : ∀ entry : PhysicalEntry M J target.length,
      (coarseIndexedEntryBinaryCost N B (depth entry) (physicalSource source entry.1)
        (substring target entry.2.lo entry.2.hi) (coarse entry) : ℝ) ≤
        C * ((coarseInitialArrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
          (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (coarse entry) : ℝ) +
          ((physicalSource source entry.1).length + 1 : ℕ))) :
    physicalFamilyIndexedCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw depth bits encode root coarse ≤ C *
      (physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta draw B depth bits encode root coarse +
       physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta
        (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        draw bits encode root) := by
  unfold physicalFamilyIndexedCoarseWork physicalFamilyMemoCoarseWork physicalFamilyCoarseInputWork
  exact coarseIndexedEntryCostSum_bound source target N depth coarse _ C hc

end Coarse
end EditApproximation

end OAI
