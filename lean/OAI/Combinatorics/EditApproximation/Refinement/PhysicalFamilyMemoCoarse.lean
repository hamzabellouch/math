import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyCoarseWork
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomCoarseKeys
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

open MeasureTheory

private theorem selectionIndicator_le {p q : Prop} (h : p → q) :
    selectionIndicator p ≤ selectionIndicator q := by
  classical
  by_cases hp : p
  · have hq := h hp
    simp only [selectionIndicator, hp, hq, ite_true, le_refl]
  · simp only [selectionIndicator, hp, ite_false]
    split <;> norm_num

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)
  (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
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



omit [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] in
 theorem physicalFamilyMemoCoarseWork_le (hP : 0 < P) (bits : ℕ) (encode : Sum Key Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) :
    physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth bits encode root coarse ≤
    physicalFamilyCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth root coarse := by
  classical
  let initial := clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse)
  have hkey (entry : PhysicalEntry M J target.length) :=
    chargedRandomMemo_coarse_key source target N P ell exponent H (ell ^ 80) T S
      (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger answer initial
      (physicalFamilyRequestValue source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      bits encode hinjective hbounded root entry
  unfold physicalFamilyMemoCoarseWork physicalFamilyCoarseWork coarseFirstRequestWork
  apply Finset.sum_le_sum
  intro entry _
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact selectionIndicator_le (hkey entry)


 theorem physicalFamilyMemoCoarseWork_expected_le (hP : 0 < P) (hN : 0 < N)
    (hell : 200 ≤ ell) (hB : B = (integerParameters N).B)
    (hsize : source.length + target.length ≤ N)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (bits : ℕ) (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (root : Table) (hroot : root.depth = J)
    (budget : ℝ)
    (hwidth : ∀ coarse : PhysicalCoarseDraw source target B depth,
      ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        hP draw root).widthWork M source.length : ℝ) ≤ budget) :
    (∫ coarse, physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth bits encode root coarse
      ∂coarseFullSeedMeasure B depth
        (fun entry => physicalSource source entry.1)
        (fun entry => substring target entry.2.lo entry.2.hi)) ≤
    budget * computedCoarseWidthOverhead N := by
  classical
  apply (integral_mono Integrable.of_finite Integrable.of_finite (fun coarse =>
    physicalFamilyMemoCoarseWork_le source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth hP bits encode hinjective hbounded root coarse)).trans
  exact physicalFamilyCoarseWork_expected_le source target N P H T S passes copies factor multiplier
    tau eta kappa delta draw B depth hP hN hell hB hsize hdepth hinverse root hroot budget hwidth

end Coarse

end EditApproximation

end OAI
