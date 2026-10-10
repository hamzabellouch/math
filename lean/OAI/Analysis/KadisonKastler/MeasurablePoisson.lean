import OAI.Analysis.KadisonKastler.PoissonNormContinuity

namespace OAI

/-! # Poisson integration of bounded vector-measurable operator fields

The analytic multiplier fields need only be measurable on each vector.
These averages therefore use vector integrals, without asserting norm
measurability of a field valued in the bounded operators.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cauchyMeasure_absolutelyContinuous (t : ℝ) {r : ℝ} (hr : 0 < r) :
    cauchyMeasure t (NNReal.mk r hr.le) ≪ volume := by
  rw [cauchyMeasure_of_scale_ne_zero t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h))]
  exact withDensity_absolutelyContinuous _ _

def measurablePoissonAverage (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  probabilityOperatorIntegral (cauchyMeasure t (NNReal.mk r hr.le)) F
    (fun x => AEStronglyMeasurable.mono_ac (cauchyMeasure_absolutelyContinuous t hr) (hF x))
    C ((cauchyMeasure_absolutelyContinuous t hr).ae_le hC)

omit [CompleteSpace H] in
theorem measurablePoissonAverage_apply (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) (x : H) :
    measurablePoissonAverage F hF C hC t r hr x =
      ∫ s, realPoissonKernel t r s • F s x := by
  change (∫ s, F s x ∂cauchyMeasure t (NNReal.mk r hr.le)) = _
  rw [cauchyMeasure_of_scale_ne_zero t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h)),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF t (NNReal.mk r hr.le))
      (ae_of_all _ fun s => ENNReal.ofReal_lt_top)]
  congr 1
  funext s
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h)) s).le,
    ← realPoissonKernel_eq_cauchyPDFReal t s hr.le]

omit [CompleteSpace H] in
theorem norm_measurablePoissonAverage_le (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) :
    ‖measurablePoissonAverage F hF C hC t r hr‖ ≤ C :=
  norm_probabilityOperatorIntegral_le _ _ _ hC0 _

omit [CompleteSpace H] in
/-- Averaging preserves an essential uniform approximation bound. -/
theorem norm_measurablePoissonAverage_sub_le (F G : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (hG : ∀ x, AEStronglyMeasurable (fun s => G s x) volume)
    (C D : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (hD : ∀ᵐ s, ‖G s‖ ≤ D)
    {e : ℝ} (he : 0 ≤ e) (hFG : ∀ᵐ s, ‖F s - G s‖ ≤ e)
    (t r : ℝ) (hr : 0 < r) :
    ‖measurablePoissonAverage F hF C hC t r hr -
      measurablePoissonAverage G hG D hD t r hr‖ ≤ e :=
  norm_probabilityOperatorIntegral_sub_le _ _ _ _ _ C D _ _ he
    ((cauchyMeasure_absolutelyContinuous t hr).ae_le hFG)

theorem measurablePoissonAverage_eq_poissonVectorAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage F (fun x => (hF x).aestronglyMeasurable) C
      (ae_of_all _ hC) t r hr = poissonVectorAverage F hF C hC t r := by
  ext x
  rw [measurablePoissonAverage_apply, poissonVectorAverage_apply_eq_integral F hF C hC t hr x]

omit [CompleteSpace H] in
private theorem integrable_measurablePoisson_vector
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t : ℝ) {r : ℝ} (hr : 0 < r) (x : H) :
    Integrable (fun s => realPoissonKernel t r s • F s x) := by
  have hm : AEStronglyMeasurable (realPoissonKernel t r) volume :=
    (integrable_realPoissonKernel t hr).aestronglyMeasurable
  apply ((integrable_realPoissonKernel t hr).mul_const (C * ‖x‖)).mono' (hm.smul (hF x))
  filter_upwards [hC] with s hs
  change ‖realPoissonKernel t r s • F s x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg t s hr)]
  exact mul_le_mul_of_nonneg_left
    (((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
    (realPoissonKernel_nonneg t s hr)

omit [CompleteSpace H] in
/-- An essentially bounded vector-measurable boundary field yields an
operator-norm Lipschitz function on every horizontal line of positive height. -/
theorem norm_measurablePoissonAverage_translate_sub_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (t u r : ℝ) (hr : 0 < r) :
    ‖measurablePoissonAverage F hF C hC t r hr -
      measurablePoissonAverage F hF C hC u r hr‖ ≤ (2 * C / r) * |t - u| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖measurablePoissonAverage F hF C hC t r hr x -
    measurablePoissonAverage F hF C hC u r hr x‖ ≤ _
  rw [measurablePoissonAverage_apply, measurablePoissonAverage_apply,
    ← integral_sub (integrable_measurablePoisson_vector F hF hC t hr x)
      (integrable_measurablePoisson_vector F hF hC u hr x)]
  have hi := ((integrable_realPoissonKernel t hr).add
    (integrable_realPoissonKernel u hr)).const_mul (|t - u| / r)
  have hb : ‖∫ s, realPoissonKernel t r s • F s x -
      realPoissonKernel u r s • F s x‖ ≤
      ∫ s, ((|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s)) *
        (C * ‖x‖) := by
    apply norm_integral_le_of_norm_le (hi.mul_const (C * ‖x‖))
    filter_upwards [hC] with s hs
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_realPoissonKernel_sub_le t u s hr)
      (((F s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
      (norm_nonneg _) (mul_nonneg (div_nonneg (abs_nonneg _) hr.le)
        (add_nonneg (realPoissonKernel_nonneg t s hr) (realPoissonKernel_nonneg u s hr)))
  calc
    _ ≤ _ := hb
    _ = (2 * C / r) * |t - u| * ‖x‖ := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (integrable_realPoissonKernel t hr) (integrable_realPoissonKernel u hr),
        integral_realPoissonKernel t hr, integral_realPoissonKernel u hr]
      ring

omit [CompleteSpace H] in
theorem continuous_measurablePoissonAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (r : ℝ) (hr : 0 < r) :
    Continuous (fun t => measurablePoissonAverage F hF C hC t r hr) := by
  have h : LipschitzWith (NNReal.mk (2 * C / r) (by positivity))
      (fun t => measurablePoissonAverage F hF C hC t r hr) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_measurablePoissonAverage_translate_sub_le F hF hC0 hC t u r hr
  exact h.continuous

end

end KadisonKastler

end OAI
