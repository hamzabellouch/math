import OAI.Geometry.SurfaceImmersion.Geometry.ConvolutionDerivativeBounds

namespace OAI

/-! Scale-exact derivative gains for convolution by the constructed kernels. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

lemma norm_iterated_dilate {K : Base → ℝ} (hK : ContDiff ℝ ∞ K)
    {s : ℝ} (hs : 0 < s) (n : ℕ) (x : Base) :
    ‖iteratedFDeriv ℝ n (dilate K s) x‖ =
      (s ^ 2)⁻¹ * (s ^ n)⁻¹ * ‖iteratedFDeriv ℝ n K (s⁻¹ • x)‖ := by
  have heq : dilate K s = (s ^ 2)⁻¹ • (fun y : Base => K (s⁻¹ • y)) := rfl
  have hc : ContDiff ℝ (n : ℕ∞ω) (fun y : Base => K (s⁻¹ • y)) :=
    (hK.comp (contDiff_id.const_smul s⁻¹)).of_le (by simp)
  rw [heq, iteratedFDeriv_const_smul_apply (f := fun y : Base => K (s⁻¹ • y)) hc.contDiffAt]
  rw [congrFun (iteratedFDeriv_comp_const_smul s⁻¹ (hK.of_le (by simp))) x]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow,
    abs_of_pos hs, inv_pow]
  ring

lemma integral_norm_iterated_dilate {K : Base → ℝ} (hK : ContDiff ℝ ∞ K)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∫ x, ‖iteratedFDeriv ℝ n (dilate K s) x‖) =
      (s ^ n)⁻¹ * ∫ x, ‖iteratedFDeriv ℝ n K x‖ := by
  have hdim : Module.finrank ℝ Base = 2 := by simp [Base]
  simp_rw [norm_iterated_dilate hK hs]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x => ‖iteratedFDeriv ℝ n K x‖) hs.le, hdim, smul_eq_mul]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An arbitrarily high output derivative is bounded by the zeroth input
norm and the corresponding fixed kernel derivative mass. -/
theorem smooth_derivative_gain (r n : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ n (smooth r s f) x‖ ≤
      (s ^ n)⁻¹ * (∫ y, ‖iteratedFDeriv ℝ n (kernel r) y‖) * C := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0)
  have h := convolution_iterated_norm_le (lsmul ℝ ℝ)
    n (smooth_dilate (kernel_smooth r) s) (compact_dilate (kernel_compact r) hs.ne') hf hb x
  change ‖iteratedFDeriv ℝ n (smooth r s f) x‖ ≤ _ at h
  apply h.trans
  rw [integral_norm_iterated_dilate (kernel_smooth r) hs]
  calc
    _ ≤ 1 * ((s ^ n)⁻¹ * ∫ y, ‖iteratedFDeriv ℝ n (kernel r) y‖) * C := by
      gcongr
      exact opNorm_lsmul_le
    _ = _ := by rw [one_mul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
