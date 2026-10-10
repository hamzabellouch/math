import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowSubstitution

namespace OAI

/-! A uniform Fourier kernel for all relative windows up to a given size.
No multiplicativity assumptions enter this finite analytic estimate. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

noncomputable def mrtWindowKernel (r t : ℝ) : ℝ :=
  min (16 * r^2) (25 / (1+t^2))

lemma mrt_log_dirichlet_norm (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖mrtLogDirichlet S a t‖ ≤
      ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ)) := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, neg_one_mul, le_refl]

lemma mrt_log_dirichlet_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (mrtLogDirichlet S a) := by
  unfold mrtLogDirichlet
  fun_prop

lemma mrt_window_kernel_integrable (S : Finset ℕ) (a : ℕ → ℂ) (r : ℝ) :
    Integrable (fun t => mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2) := by
  let C := ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ))
  have hm : Measurable (fun t => mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2) := by
    unfold mrtWindowKernel mrtLogDirichlet
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (25*C^2)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  have hn : 0 ≤ mrtWindowKernel r t := le_min (by positivity) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (sq_nonneg _))]
  have hC : ‖mrtLogDirichlet S a t‖^2 ≤ C^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm S a t) 2
  calc
    _ ≤ (25/(1+t^2))*C^2 := mul_le_mul (min_le_right _ _) hC (sq_nonneg _)
      (by positivity)
    _ = _ := by ring

lemma mrt_window_frequency_integrable (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    Integrable (fun t => ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖^2) := by
  let C := ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ))
  have hm : Measurable (fun t => ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖^2) := by
    unfold mrtWindowMultiplier mrtLogDirichlet
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul ((Real.exp v+1)^2*C^2)).mono'
    hm.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  have hC : ‖mrtLogDirichlet S a t‖^2 ≤ C^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm S a t) 2
  calc
    _ ≤ ((Real.exp v+1)^2/(1+t^2))*C^2 :=
      mul_le_mul (mrt_window_multiplier_sq v t) hC (sq_nonneg _) (by positivity)
    _ = _ := by ring

theorem mrt_log_window_uniform_kernel (S : Finset ℕ) (a : ℕ → ℂ)
    {u r : ℝ} (hu : 0 ≤ u) (hur : u ≤ r) (hr : r ≤ 3) :
    (∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) ≤
      (2*Real.pi)⁻¹ *
        ∫ t : ℝ, mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2 := by
  rw [mrt_log_window_energy_angular S a (Real.log_nonneg (by linarith))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (mrt_window_frequency_integrable S a _)
    (mrt_window_kernel_integrable S a r)
  intro t
  change ‖mrtWindowMultiplier (Real.log (1+u)) t * mrtLogDirichlet S a t‖^2 ≤ _
  rw [norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply (mrt_relative_window_multiplier hu (hur.trans hr) t).trans
  exact min_le_min (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hu hur 2) (by norm_num)) le_rfl

lemma mrt_log_window_joint_measurable (S : Finset ℕ) (a : ℕ → ℂ) :
    Measurable (fun z : ℝ × ℝ => mrtLogWindow S a (Real.log (1+z.1)) z.2) := by
  apply Finset.measurable_sum
  intro n _
  apply measurable_const.mul
  unfold mrtLogWindowAtom
  simp only [indicator_apply]
  apply Measurable.ite _ (by fun_prop) measurable_const
  exact (measurableSet_le (by fun_prop) measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_const)

lemma mrt_log_window_energy_measurable (S : Finset ℕ) (a : ℕ → ℂ) :
    Measurable (fun u : ℝ => ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) := by
  exact ((mrt_log_window_joint_measurable S a).norm.pow_const 2).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

lemma mrt_log_window_energy_intervalIntegrable (S : Finset ℕ) (a : ℕ → ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr3 : r ≤ 3) :
    IntervalIntegrable
      (fun u => ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) volume 0 r := by
  let C := (2*Real.pi)⁻¹ *
    ∫ t : ℝ, mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2
  rw [intervalIntegrable_iff, uIoc_of_le hr0]
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (mrt_log_window_energy_measurable S a).aestronglyMeasurable (M := C)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact mrt_log_window_uniform_kernel S a hu.1.le hu.2 hr3

theorem mrt_log_window_kernel_average (S : Finset ℕ) (a : ℕ → ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr3 : r ≤ 3) :
    (∫ u in 0..r, ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) ≤
      r * (2*Real.pi)⁻¹ *
        ∫ t : ℝ, mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2 := by
  have hb := intervalIntegral.integral_mono_on hr0
    (mrt_log_window_energy_intervalIntegrable S a hr0 hr3) intervalIntegrable_const
    (fun u hu => mrt_log_window_uniform_kernel S a hu.1 hu.2 hr3)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using hb

end TwoPointCorrelations

end OAI
