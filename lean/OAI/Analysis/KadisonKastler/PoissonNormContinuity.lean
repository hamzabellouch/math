import OAI.Analysis.KadisonKastler.PoissonKernelContinuity

namespace OAI

/-! # Norm continuity of vectorwise Poisson averages

Although the boundary field is only strongly continuous, translating the
integrable scalar kernel gives norm continuity of each positive-height
operator average.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem continuous_realPoissonKernel (t : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (realPoissonKernel t r) := by
  unfold realPoissonKernel
  apply continuous_const.div
    (continuous_const.mul (((continuous_const.sub continuous_id).pow 2).add continuous_const))
  intro s
  exact ne_of_gt (mul_pos Real.pi_pos
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hr)))

omit [CompleteSpace H] in
private theorem integrable_poisson_vector
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    {C : ℝ} (hC : ∀ s, ‖F s‖ ≤ C) (t : ℝ) {r : ℝ} (hr : 0 < r) (x : H) :
    Integrable (fun s => realPoissonKernel t r s • F s x) := by
  apply ((integrable_realPoissonKernel t hr).mul_const (C * ‖x‖)).mono'
    (((continuous_realPoissonKernel t hr).smul (hF x)).aestronglyMeasurable)
  filter_upwards [] with s
  change ‖realPoissonKernel t r s • F s x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg t s hr)]
  exact mul_le_mul_of_nonneg_left
    (((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC s) (norm_nonneg x)))
    (realPoissonKernel_nonneg t s hr)

/-- A quantitative translation bound independent of the boundary field's
modulus of strong continuity. -/
theorem norm_poissonVectorAverage_sub_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖F s‖ ≤ C)
    (t u : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖poissonVectorAverage F hF C hC t r - poissonVectorAverage F hF C hC u r‖ ≤
      (2 * C / r) * |t - u| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖poissonVectorAverage F hF C hC t r x -
    poissonVectorAverage F hF C hC u r x‖ ≤ _
  rw [poissonVectorAverage_apply_eq_integral F hF C hC t hr x,
    poissonVectorAverage_apply_eq_integral F hF C hC u hr x,
    ← integral_sub (integrable_poisson_vector F hF hC t hr x)
      (integrable_poisson_vector F hF hC u hr x)]
  have hi := ((integrable_realPoissonKernel t hr).add
    (integrable_realPoissonKernel u hr)).const_mul (|t - u| / r)
  have hbound : ‖∫ s, realPoissonKernel t r s • F s x -
      realPoissonKernel u r s • F s x‖ ≤
      ∫ s, ((|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s)) *
        (C * ‖x‖) := by
    apply norm_integral_le_of_norm_le (hi.mul_const (C * ‖x‖))
    filter_upwards [] with s
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_realPoissonKernel_sub_le t u s hr)
      (((F s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hC s) (norm_nonneg x)))
      (norm_nonneg _) (mul_nonneg (div_nonneg (abs_nonneg _) hr.le)
        (add_nonneg (realPoissonKernel_nonneg t s hr) (realPoissonKernel_nonneg u s hr)))
  calc
    _ ≤ _ := hbound
    _ = (2 * C / r) * |t - u| * ‖x‖ := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (integrable_realPoissonKernel t hr) (integrable_realPoissonKernel u hr),
        integral_realPoissonKernel t hr, integral_realPoissonKernel u hr]
      ring

/-- Positive-height Poisson smoothing is continuous in operator norm. -/
theorem continuous_poissonVectorAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖F s‖ ≤ C)
    {r : ℝ} (hr : 0 < r) :
    Continuous (fun t => poissonVectorAverage F hF C hC t r) := by
  have h : LipschitzWith ⟨2 * C / r, by positivity⟩
      (fun t => poissonVectorAverage F hF C hC t r) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_poissonVectorAverage_sub_le F hF hC0 hC t u hr
  exact h.continuous

end

end KadisonKastler

end OAI
