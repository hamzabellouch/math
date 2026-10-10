import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAdditiveWindows

namespace OAI

/-! Rectangular integration of the finite additive windows. The two-window
inequality pays its error once before logarithmic Fourier analysis. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

lemma mrt_interval_sum_sq_box (S : Finset ℕ) (a : ℕ → ℂ)
    (b c d e : ℝ) :
    Integrable (fun z : ℝ × ℝ => ‖mrtIntervalSum S a z.1 z.2‖ ^ 2)
      ((volume.restrict (Ioc b c)).prod (volume.restrict (Ioc d e))) := by
  apply integrableOn_univ.mp
  exact mrt_interval_sum_sq_integrableOn S a (measure_ne_top _ _)
    measurable_fst measurable_snd

lemma mrt_interval_sum_sq_inner (S : Finset ℕ) (a : ℕ → ℂ)
    (b c : ℝ) {d e : ℝ} (hde : d ≤ e) :
    IntervalIntegrable (fun x => ∫ w in d..e, ‖mrtIntervalSum S a x w‖ ^ 2)
      volume b c := by
  rw [intervalIntegrable_iff]
  simp_rw [intervalIntegral.integral_of_le hde]
  exact (mrt_interval_sum_sq_box S a (min b c) (max b c) d e).integral_prod_left

lemma mrt_interval_sum_sq_swap (S : Finset ℕ) (a : ℕ → ℂ)
    {b c d e : ℝ} (hbc : b ≤ c) (hde : d ≤ e) :
    (∫ x in b..c, ∫ w in d..e, ‖mrtIntervalSum S a x w‖ ^ 2) =
      ∫ w in d..e, ∫ x in b..c, ‖mrtIntervalSum S a x w‖ ^ 2 := by
  simp_rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hde]
  exact integral_integral_swap (mrt_interval_sum_sq_box S a b c d e)

theorem mrt_additive_window_rectangular (S : Finset ℕ) (a : ℕ → ℂ)
    {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2 * N, ‖mrtIntervalSum S a x h‖ ^ 2) ≤
      (2 / h) * ∫ x in N..3 * N, ∫ w in 0..3 * h,
        ‖mrtIntervalSum S a x w‖ ^ 2 := by
  let A : ℝ → ℝ := fun x => ∫ w in 0..3 * h, ‖mrtIntervalSum S a x w‖ ^ 2
  have hAi (b c : ℝ) : IntervalIntegrable A volume b c :=
    mrt_interval_sum_sq_inner S a b c (by positivity)
  have hApos (x : ℝ) : 0 ≤ A x :=
    intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _)
  have hp (x : ℝ) : ‖mrtIntervalSum S a x h‖ ^ 2 ≤ h⁻¹ * (A x + A (x + h)) := by
    apply (mrt_interval_sum_averaged_sq S a x hh).trans
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
    apply add_le_add
    · exact intervalIntegral.integral_mono_interval hh.le (by linarith) le_rfl
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (mrt_interval_sum_sq_intervalIntegrable S a measurable_const measurable_id 0 (3*h))
    · rw [show (∫ w in h..3*h, ‖mrtIntervalSum S a (x+h) (w-h)‖ ^ 2) =
          ∫ w in 0..2*h, ‖mrtIntervalSum S a (x+h) w‖ ^ 2 by
          have he : 3*h-h = 2*h := by ring
          simpa only [sub_self, he] using intervalIntegral.integral_comp_sub_right
            (a := h) (b := 3*h)
            (fun w => ‖mrtIntervalSum S a (x+h) w‖ ^ 2) h]
      exact intervalIntegral.integral_mono_interval le_rfl (by positivity) (by linarith)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (mrt_interval_sum_sq_intervalIntegrable S a measurable_const measurable_id 0 (3*h))
  have hshift : (∫ x in N..2*N, A (x+h)) = ∫ x in N+h..2*N+h, A x := by
    exact intervalIntegral.integral_comp_add_right A h
  have hshiftI : IntervalIntegrable (fun x => A (x+h)) volume N (2*N) := by
    simpa only [add_sub_cancel_right] using (hAi (N+h) (2*N+h)).comp_add_right h
  have hi := intervalIntegral.integral_mono_on (by linarith : N ≤ 2*N)
    (mrt_interval_sum_sq_intervalIntegrable S a measurable_id measurable_const N (2*N))
    (((hAi N (2*N)).add hshiftI).const_mul h⁻¹) (fun x _ => hp x)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (hAi N (2*N)) hshiftI, hshift] at hi
  have h₁ : (∫ x in N..2*N, A x) ≤ ∫ x in N..3*N, A x :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall hApos) (hAi N (3*N))
  have h₂ : (∫ x in N+h..2*N+h, A x) ≤ ∫ x in N..3*N, A x :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hApos) (hAi N (3*N))
  calc
    _ ≤ h⁻¹ * ((∫ x in N..2*N, A x) + ∫ x in N+h..2*N+h, A x) := hi
    _ ≤ h⁻¹ * (2 * ∫ x in N..3*N, A x) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
      linarith
    _ = _ := by dsimp [A]; ring

end TwoPointCorrelations

end OAI
