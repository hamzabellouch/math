import OAI.Geometry.SurfaceImmersion.Correction.SmoothingConvolution

namespace OAI

/-! Scale-independent zeroth-order bounds for the constructed smoothing
operator, including the signed finite-moment kernels. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma norm_dilate (K : Base → ℝ) (s : ℝ) (x : Base) :
    ‖dilate K s x‖ = dilate (fun y => ‖K y‖) s x := by
  simp only [dilate, norm_mul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (sq_nonneg s)]

lemma norm_mass_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖dilate K s x‖) = ∫ x, ‖K x‖ := by
  simp_rw [norm_dilate]
  exact mass_dilate (fun x => ‖K x‖) hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Signed moment cancellation does not cost a power of the smoothing scale:
the operator bound is the fixed L1 norm of the chosen kernel. -/
lemma smooth_norm_le (r : ℕ) {s C : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖smooth r s f x‖ ≤ (∫ y, ‖kernel r y‖) * C := by
  have hk := compact_dilate (kernel_compact r) hs.ne'
  have hcont := (smooth_dilate (kernel_smooth r) s).continuous
  have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hk).norm.mul_const C
  change ‖∫ y, dilate (kernel r) s y • f (x - y)‖ ≤ _
  calc
    _ ≤ ∫ y, ‖dilate (kernel r) s y‖ * C :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun y => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hf (x - y)) (norm_nonneg _))
    _ = (∫ y, ‖kernel r y‖) * C := by rw [integral_mul_const, norm_mass_dilate _ hs]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
