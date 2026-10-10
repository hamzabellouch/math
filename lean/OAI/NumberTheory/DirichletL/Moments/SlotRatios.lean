import OAI.NumberTheory.DirichletL.Moments.DivisorBoundary

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def logWindow (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

theorem logWindow_nonneg (a b : ℝ) : 0 ≤ logWindow a b :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem slot_log_ratio_bound (W : ℝ → ℂ) (a b P Z : ℝ) (I : Ideal O)
    (ha : 0 < a) (hZ : 1 < Z)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hW : W ((Ideal.absNorm I:ℝ)/P) ≠ 0) :
    |Real.logb Z ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b/Real.log Z := by
  have hw := hs hW
  have hr : 0 < (Ideal.absNorm I:ℝ)/P := ha.trans_le hw.1
  have hlow := Real.log_le_log ha hw.1
  have hhigh := Real.log_le_log hr hw.2
  have habs : |Real.log ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (Real.log a)
      have hm := le_max_left |Real.log a| |Real.log b|
      dsimp only [logWindow]
      linarith
    · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.logb,abs_div,abs_of_pos (Real.log_pos hZ)]
  exact div_le_div_of_nonneg_right habs (Real.log_pos hZ).le

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem frozen_subset_ratio_bound (entrance frozen : Finset ι) (hsub : frozen ⊆ entrance)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ frozen,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |∑ i ∈ frozen,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  calc
    _ ≤ ∑ i ∈ frozen,|Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ frozen,logWindow (a i) (b i)/Real.log Z :=
      Finset.sum_le_sum (fun i hi => slot_log_ratio_bound (W i) (a i) (b i) (P i) Z (v i)
        (ha i (hsub hi)) hZ (hs i (hsub hi)) (hW i hi))
    _ = (∑ i ∈ frozen,logWindow (a i) (b i))/Real.log Z := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => logWindow_nonneg (a i) (b i))) (Real.log_pos hZ).le

theorem disjoint_frozen_ratio_bound (entrance old fresh : Finset ι)
    (hold : old ⊆ entrance) (hfresh : fresh ⊆ entrance) (hdis : Disjoint old fresh)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ old ∪ fresh,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |(∑ i ∈ old,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))+
      (∑ i ∈ fresh,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  rw [← Finset.sum_union hdis]
  exact frozen_subset_ratio_bound entrance (old ∪ fresh) (Finset.union_subset hold hfresh)
    W a b P v Z hZ ha hs hW

end SevenEighths.CenteredMomentSlotRatios

end

end OAI
