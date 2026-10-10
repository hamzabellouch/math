import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace OAI

/-! # Bounds for Gamma on the positive vertical strips used by the contour -/

namespace Ostmann

open Complex MeasureTheory Set

/-- The Euler integral bounds Gamma at a complex point by its real value. -/
theorem gamma_norm_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp [Complex.norm_exp]

theorem gamma_positive_strip_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C := by
  have hc : ContinuousOn Real.Gamma (Icc a b) := by
    intro x hx
    apply (Real.differentiableAt_Gamma (fun n => ?_)).continuousAt.continuousWithinAt
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hx.1]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hza hzb
  calc
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := gamma_norm_le_real z (lt_of_lt_of_le ha hza)
    _ ≤ ‖Real.Gamma z.re‖ := le_abs_self _
    _ ≤ C := hC z.re ⟨hza, hzb⟩
    _ ≤ max C 1 := le_max_left _ _

end Ostmann

end OAI
