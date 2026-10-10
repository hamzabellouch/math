import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowPlancherel

namespace OAI

/-! Uniform short-window bounds for the explicit Fourier multiplier. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Set

lemma mrt_window_multiplier_integral (a t : ℝ) :
    mrtWindowMultiplier a t =
      ∫ y in (0 : ℝ)..a, Complex.exp (((1 : ℂ) + (t : ℂ) * I) * y) := by
  rw [integral_exp_mul_complex (mrt_one_add_imaginary_ne_zero t)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mrtWindowMultiplier]

lemma mrt_window_multiplier_small {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    ‖mrtWindowMultiplier a t‖ ≤ a * Real.exp a := by
  rw [mrt_window_multiplier_integral]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := a) (C := Real.exp a)
    (f := fun y : ℝ => Complex.exp (((1 : ℂ) + (t : ℂ) * I) * y)) (fun y hy => ?_)
  · simpa only [sub_zero, abs_of_nonneg ha, mul_comm] using hh
  · rw [uIoc_of_le ha] at hy
    have he : ‖Complex.exp (((1 : ℂ) + (t : ℂ) * I) * y)‖ = Real.exp y := by
      rw [Complex.norm_exp]
      simp
    rw [he]
    exact Real.exp_le_exp.mpr hy.2

theorem mrt_relative_window_multiplier {u : ℝ} (hu : 0 ≤ u) (hu3 : u ≤ 3) (t : ℝ) :
    ‖mrtWindowMultiplier (Real.log (1 + u)) t‖ ^ 2 ≤
      min (16 * u ^ 2) (25 / (1 + t ^ 2)) := by
  have hu0 : 0 < 1 + u := by linarith
  have hlog : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hlogu : Real.log (1 + u) ≤ u := by
    have hh := Real.log_le_sub_one_of_pos hu0
    linarith
  have hsmall : ‖mrtWindowMultiplier (Real.log (1 + u)) t‖ ≤ 4 * u := by
    apply (mrt_window_multiplier_small hlog t).trans
    rw [Real.exp_log hu0]
    nlinarith [mul_le_mul_of_nonneg_right hlogu hu0.le]
  have hlarge := mrt_window_multiplier_sq (Real.log (1 + u)) t
  rw [Real.exp_log hu0] at hlarge
  apply le_min
  · have hh := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
    nlinarith
  · apply hlarge.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith

theorem mrt_log_window_energy_angular (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ y : ℝ, ‖mrtLogWindow S a v y‖ ^ 2) =
      (2 * Real.pi)⁻¹ *
        ∫ t : ℝ, ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖ ^ 2 := by
  rw [mrt_log_window_plancherel S a hv]
  simpa only [abs_of_pos (inv_pos.mpr (show (0 : ℝ) < 2 * Real.pi by positivity)),
    smul_eq_mul] using Measure.integral_comp_mul_left
      (fun t : ℝ => ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖ ^ 2)
      (2 * Real.pi)

end TwoPointCorrelations

end OAI
