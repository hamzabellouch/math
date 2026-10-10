import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! Conversion of relative additive windows to the logarithmic window,
including the physical-variable Jacobian. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

lemma mrt_log_window_measurable (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    Measurable (mrtLogWindow S a v) := by
  apply Finset.measurable_sum
  intro n _
  apply measurable_const.mul
  exact (show Measurable (fun y : ℝ => (Real.exp (-y) : ℂ)) by fun_prop).indicator
    measurableSet_Ico

lemma mrt_relative_interval_identity (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    mrtIntervalSum S a x (x * u) =
      (x : ℂ) * mrtLogWindow S a (Real.log (1 + u)) (Real.log x) := by
  rw [mrt_log_window_interval S hn a, Real.exp_neg,
    Real.exp_log hx, Real.exp_log (by linarith : 0 < 1 + u)]
  have he : ((1 + u) - 1) * x = x * u := by ring
  rw [he]
  have hc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma mrt_relative_interval_sq (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    ‖mrtIntervalSum S a x (x * u)‖ ^ 2 =
      x ^ 2 * ‖mrtLogWindow S a (Real.log (1 + u)) (Real.log x)‖ ^ 2 := by
  rw [mrt_relative_interval_identity S hn a hx hu, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx, mul_pow]

lemma mrt_log_weight_integral_bound {g : ℝ → ℝ} (hgm : Measurable g)
    (hgi : Integrable g) (hgn : ∀ y, 0 ≤ g y) {N : ℝ} (hN : 0 < N) :
    (∫ x in N..3 * N, x ^ 3 * g (Real.log x)) ≤
      (3 * N) ^ 4 * ∫ y : ℝ, g y := by
  let b : ℝ → ℝ := fun x => x⁻¹ * g (Real.log x)
  have hbi : IntegrableOn b (Ioi 0) := by
    exact (integrableOn_comp_log_Ioi_zero g).mpr hgi
  have hs : Ioc N (3*N) ⊆ Ioi (0:ℝ) := fun x hx => lt_trans hN hx.1
  have hbn : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ b x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (inv_nonneg.mpr hx.le) (hgn _)
  have hpoly (x : ℝ) (hx : x ∈ Ioc N (3*N)) :
      x ^ 3 * g (Real.log x) ≤ (3*N)^4 * b x := by
    have hx0 : 0 < x := lt_trans hN hx.1
    calc
      x ^ 3 * g (Real.log x) = x ^ 4 * b x := by
        dsimp [b]
        field_simp
      _ ≤ (3*N)^4 * b x := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hx0.le hx.2 4) (mul_nonneg (inv_nonneg.mpr hx0.le) (hgn _))
  have hdom : IntegrableOn (fun x => (3*N)^4 * b x) (Ioc N (3*N)) :=
    (hbi.mono_set hs).const_mul _
  have hleft : IntegrableOn (fun x => x^3 * g (Real.log x)) (Ioc N (3*N)) := by
    apply hdom.mono' (((measurable_id.pow_const 3).mul
      (hgm.comp Real.measurable_log)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change ‖x^3 * g (Real.log x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (lt_trans hN hx.1).le _) (hgn _))]
    exact hpoly x hx
  rw [intervalIntegral.integral_of_le (by linarith : N ≤ 3*N)]
  calc
    _ ≤ ∫ x in Ioc N (3*N), (3*N)^4 * b x :=
      setIntegral_mono_on hleft hdom measurableSet_Ioc hpoly
    _ = (3*N)^4 * ∫ x in Ioc N (3*N), b x := integral_const_mul _ _
    _ ≤ (3*N)^4 * ∫ x in Ioi (0:ℝ), b x := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hbi hbn hs.eventuallySubset) (by positivity)
    _ = _ := by
      rw [show (∫ x in Ioi (0:ℝ), b x) = ∫ y : ℝ, g y by
        exact integral_comp_log_Ioi_zero g]

theorem mrt_relative_window_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N u : ℝ} (hN : 0 < N) (hu : 0 ≤ u) :
    (∫ x in N..3*N, x * ‖mrtIntervalSum S a x (x*u)‖ ^ 2) ≤
      (3*N)^4 * ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖ ^ 2 := by
  calc
    _ = ∫ x in N..3*N,
        x^3 * ‖mrtLogWindow S a (Real.log (1+u)) (Real.log x)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      change x * ‖mrtIntervalSum S a x (x*u)‖ ^ 2 = _
      rw [uIcc_of_le (by linarith : N ≤ 3*N)] at hx
      rw [mrt_relative_interval_sq S hn a (lt_of_lt_of_le hN hx.1) hu]
      ring
    _ ≤ _ := mrt_log_weight_integral_bound
      ((mrt_log_window_measurable S a _).norm.pow_const 2)
      ((mrt_log_window_memLp S a _).integrable_norm_pow (by norm_num))
      (fun _ => sq_nonneg _) hN

end TwoPointCorrelations

end OAI
