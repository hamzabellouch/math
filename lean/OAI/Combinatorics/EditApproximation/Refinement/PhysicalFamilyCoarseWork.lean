import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyWork
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomCoarseWork
import OAI.Combinatorics.EditApproximation.Coarse.CoarseFirstRequestCost
import OAI.Combinatorics.EditApproximation.Geometry.BalancedWidths
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseSeedLaw

namespace OAI

namespace EditApproximation

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

noncomputable def physicalFamilyCoarseQuery
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    FiniteQuery (PhysicalEntry M J target.length) :=
  chargedRandomCoarseQuery source target N P ell exponent H (ell ^ 80) T S (passes + 1)
    copies factor multiplier tau eta kappa delta readGroup readInteger answer root

 theorem physicalFamilyCoarseQuery_cost_le_width
    (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S)
    (hroot : root.depth = J) :
    (physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw root).cost (fun entry => (initial entry : ℚ))
      (fun entry => (physicalSource source entry.1).length) ≤
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length := by
  apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans
    (chargedRandomCoarseQuery_width_cost_le source target N P H T S (passes + 1) copies
      factor multiplier tau eta kappa delta readGroup readInteger answer initial group
      (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta hP draw initial)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw) root hroot)
  intro entry
  rw [physicalSource_length_eq]
  exact (sourceIntervalAt_width M source.length entry.1.1.val (Nat.pos_of_neZero M) entry.1.2).trans
    (Nat.le_add_left _ 1)

variable (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

noncomputable def physicalFamilyCoarseWork
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S)
    (coarse : PhysicalCoarseDraw source target B depth) : ℝ :=
  coarseFirstRequestWork N B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
    (physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw root) coarse

 theorem physicalFamilyCoarseWork_expected_le
    (hP : 0 < P) (hN : 0 < N) (hell : 200 ≤ ell)
    (hB : B = (integerParameters N).B) (hsize : source.length + target.length ≤ N)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S)
    (hroot : root.depth = J) (budget : ℝ)
    (hwidth : ∀ coarse : PhysicalCoarseDraw source target B depth,
      ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        hP draw root).widthWork M source.length : ℝ) ≤ budget) :
    (∫ coarse, physicalFamilyCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth root coarse
      ∂coarseFullSeedMeasure B depth
        (fun entry => physicalSource source entry.1)
        (fun entry => substring target entry.2.lo entry.2.hi)) ≤
    budget * computedCoarseWidthOverhead N := by
  have hentries (entry : PhysicalEntry M J target.length) :
      coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) ≤ N := by
    apply max_le
    · exact (physicalSource_length_le source entry.1).trans (by omega)
    · have hl : (substring target entry.2.lo entry.2.hi).length ≤ target.length := by
        simp only [substring, List.length_drop, List.length_take]
        exact (Nat.sub_le _ _).trans (min_le_right _ _)
      exact hl.trans (by omega)
  apply coarseFirstRequestWork_expected_le N B depth _ _ _ hB hN hell hdepth hentries hinverse budget
  intro coarse
  have hc := physicalFamilyCoarseQuery_cost_le_width source target N P H T S passes copies
    factor multiplier tau eta kappa delta draw
    (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse)) hP root hroot
  exact ((Nat.cast_le (α := ℝ)).mpr hc).trans (hwidth coarse)

end Coarse

end EditApproximation

end OAI
