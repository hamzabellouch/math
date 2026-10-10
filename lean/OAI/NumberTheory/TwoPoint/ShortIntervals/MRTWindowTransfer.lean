import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowAveraging
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowKernel

namespace OAI

/-! The fixed additive-window mean square is controlled by the actual
finite logarithmic Dirichlet polynomial. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

private lemma relative_box_integrable (S : Finset ℕ) (a : ℕ → ℂ)
    {N : ℝ} (hN : 0 < N) (r : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.1 * ‖mrtIntervalSum S a z.1 (z.1*z.2)‖^2)
      ((volume.restrict (Ioc N (3*N))).prod (volume.restrict (Ioc 0 r))) := by
  rw [Measure.prod_restrict]
  apply Measure.integrableOn_of_bounded
    (by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne)
    (by
      exact (measurable_fst.mul
        ((mrt_interval_sum_measurable S a measurable_fst
          (measurable_fst.mul measurable_snd)).norm.pow_const 2)).aestronglyMeasurable)
    (M := 3*N*(∑ n ∈ S, ‖a n‖)^2)
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  have hx : 0 < z.1 := lt_trans hN hz.1.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le (sq_nonneg _))]
  exact mul_le_mul hz.1.2
    (pow_le_pow_left₀ (norm_nonneg _) (mrt_interval_sum_norm S a _ _) 2)
    (sq_nonneg _) (by positivity)

private lemma relative_rescale (S : Finset ℕ) (a : ℕ → ℂ)
    {x H r : ℝ} (hH : 0 ≤ H) (hHr : H ≤ x*r) :
    (∫ w in 0..H, ‖mrtIntervalSum S a x w‖^2) ≤
      ∫ u in 0..r, x * ‖mrtIntervalSum S a x (x*u)‖^2 := by
  calc
    _ ≤ ∫ w in 0..x*r, ‖mrtIntervalSum S a x w‖^2 :=
      intervalIntegral.integral_mono_interval le_rfl hH hHr
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (mrt_interval_sum_sq_intervalIntegrable S a (x := fun _ => x) (h := id)
          measurable_const measurable_id _ _)
    _ = x * ∫ u in 0..r, ‖mrtIntervalSum S a x (x*u)‖^2 := by
      simpa only [mul_zero, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (a := 0) (b := r) (fun w => ‖mrtIntervalSum S a x w‖^2) x).symm
    _ = _ := (intervalIntegral.integral_const_mul _ _).symm

theorem mrt_fixed_window_log_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2*N, ‖mrtIntervalSum S a x h‖^2) ≤
      (162 * N^4 / h) *
        ∫ u in 0..(3*h/N), ∫ y : ℝ,
          ‖mrtLogWindow S a (Real.log (1+u)) y‖^2 := by
  let r : ℝ := 3*h/N
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr3 : r ≤ 3 := by dsimp [r]; apply (div_le_iff₀ hN).mpr; linarith
  have hi := relative_box_integrable S a hN r
  have hleft : IntervalIntegrable
      (fun x => ∫ w in 0..3*h, ‖mrtIntervalSum S a x w‖^2) volume N (3*N) :=
    mrt_interval_sum_sq_inner S a _ _ (by positivity)
  have hright : IntervalIntegrable
      (fun x => ∫ u in 0..r, x * ‖mrtIntervalSum S a x (x*u)‖^2)
      volume N (3*N) := by
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : N ≤ 3*N)]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hr0] using! hi.integral_prod_left
  have hres := intervalIntegral.integral_mono_on (by linarith : N ≤ 3*N)
    hleft hright (fun x hx => relative_rescale S a
      (by positivity) (by
        dsimp [r]
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hN).mpr
        have := mul_le_mul_of_nonneg_right hx.1 (show 0 ≤ 3*h by positivity)
        nlinarith))
  have hswap :
      (∫ x in N..3*N, ∫ u in 0..r, x * ‖mrtIntervalSum S a x (x*u)‖^2) =
      ∫ u in 0..r, ∫ x in N..3*N, x * ‖mrtIntervalSum S a x (x*u)‖^2 := by
    simp_rw [intervalIntegral.integral_of_le (by linarith : N ≤ 3*N),
      intervalIntegral.integral_of_le hr0]
    exact integral_integral_swap hi
  have houter : IntervalIntegrable
      (fun u => ∫ x in N..3*N, x * ‖mrtIntervalSum S a x (x*u)‖^2)
      volume 0 r := by
    rw [intervalIntegrable_iff, uIoc_of_le hr0]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le (by linarith : N ≤ 3*N)] using!
      hi.integral_prod_right
  have hlog := intervalIntegral.integral_mono_on hr0 houter
    ((mrt_log_window_energy_intervalIntegrable S a hr0 hr3).const_mul ((3*N)^4))
    (fun u hu => mrt_relative_window_energy S hn a hN hu.1)
  rw [intervalIntegral.integral_const_mul] at hlog
  calc
    _ ≤ (2/h) * ∫ x in N..3*N, ∫ w in 0..3*h,
        ‖mrtIntervalSum S a x w‖^2 := mrt_additive_window_rectangular S a hN hh hhN
    _ ≤ (2/h) * ∫ x in N..3*N, ∫ u in 0..r,
        x * ‖mrtIntervalSum S a x (x*u)‖^2 :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ = (2/h) * ∫ u in 0..r, ∫ x in N..3*N,
        x * ‖mrtIntervalSum S a x (x*u)‖^2 := by rw [hswap]
    _ ≤ (2/h) * ((3*N)^4 * ∫ u in 0..r, ∫ y : ℝ,
        ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by dsimp [r]; ring

theorem mrt_fixed_window_fourier_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2*N, ‖mrtIntervalSum S a x h‖^2) ≤
      (486 * N^3 / (2*Real.pi)) *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2 := by
  have hr0 : 0 ≤ 3*h/N := by positivity
  have hr3 : 3*h/N ≤ 3 := by apply (div_le_iff₀ hN).mpr; linarith
  calc
    _ ≤ (162*N^4/h) * ∫ u in 0..(3*h/N), ∫ y : ℝ,
        ‖mrtLogWindow S a (Real.log (1+u)) y‖^2 :=
      mrt_fixed_window_log_energy S hn a hN hh hhN
    _ ≤ (162*N^4/h) * ((3*h/N)*(2*Real.pi)⁻¹ *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) :=
      mul_le_mul_of_nonneg_left (mrt_log_window_kernel_average S a hr0 hr3) (by positivity)
    _ = _ := by field_simp; ring

end TwoPointCorrelations

end OAI
