import OAI.Geometry.SurfaceImmersion.Correction.FiniteSmootherLinearity

namespace OAI

/-! Weighted bounds for finite-order smoothing in the chart norms used by
the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothing at one scale remains bounded in the original weighted norm
at any other positive scale. -/
theorem finiteSmooth_weighted_bounded (n m : ℕ) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : WeightedBound Set.univ t m C f) :
    WeightedBound Set.univ t m ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ n) * C)
      (finiteSmooth n s f) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  have h := finiteSmooth_bounded n j hs hf hfc (C := C / t ^ j)
    (fun y => by simpa only [iteratedFDerivWithin_univ] using hb.deriv_le ht hj (Set.mem_univ y)) x
  calc
    _ ≤ t ^ j * ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ n) * (C / t ^ j)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg ht.le _)
    _ = _ := by field_simp

def weightedGainConstant (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), gainConstant n j

lemma weightedGainConstant_nonneg (n m : ℕ) : 0 ≤ weightedGainConstant n m :=
  Finset.sum_nonneg (fun j _ => gainConstant_nonneg n j)

/-- Every weighted output derivative is controlled by the zeroth input
norm; higher input derivatives do not enter the constant. -/
theorem finiteSmooth_weighted_gain (n m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hb : ∀ x, ‖f x‖ ≤ C) :
    WeightedBound Set.univ s m (weightedGainConstant n m * C) (finiteSmooth n s f) := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0)
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  have h := finiteSmooth_gain n j hs hf hb x
  have hsum : gainConstant n j ≤ weightedGainConstant n m :=
    Finset.single_le_sum (fun i _ => gainConstant_nonneg n i) (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ s ^ j * ((s ^ j)⁻¹ * gainConstant n j * C) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hs.le _)
    _ = gainConstant n j * C := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum hC

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
