import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RegularizedSlowSolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-! # Polynomial growth of the regularizing bracket at infinity -/

namespace DefocusingNLS

theorem norm_cpow_le_rpow_max (z w : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖z ^ w‖ ≤ Real.exp (Real.pi * |w.im|) * ‖z‖ ^ (max w.re 0) := by
  have harg : -(z.arg * w.im) ≤ Real.pi * |w.im| := by
    calc
      -(z.arg * w.im) ≤ |z.arg * w.im| := neg_le_abs _
      _ = |z.arg| * |w.im| := abs_mul _ _
      _ ≤ Real.pi * |w.im| :=
        mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
  calc
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (-(z.arg * w.im)) := by
      simpa only [div_eq_mul_inv, ← Real.exp_neg] using Complex.norm_cpow_le z w
    _ ≤ ‖z‖ ^ (max w.re 0) * Real.exp (Real.pi * |w.im|) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _))
        (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

theorem norm_one_add_real_div_bounds (x : ℂ) (hx : x ≠ 0) {u : ℝ}
    (hu : max 1 (2 * ‖x‖) ≤ u) :
    1 ≤ ‖1 + (u : ℂ) / x‖ ∧
      ‖1 + (u : ℂ) / x‖ ≤ (1 + ‖x‖⁻¹) * u := by
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  have hux : 2 * ‖x‖ ≤ u := (le_max_right _ _).trans hu
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm : ‖(u : ℂ) / x‖ = u / ‖x‖ := by
    rw [norm_div, Complex.norm_of_nonneg hu0]
  constructor
  · have hlow := norm_sub_norm_le ((u : ℂ) / x) (-1)
    rw [hnorm, norm_neg, norm_one, sub_neg_eq_add, add_comm] at hlow
    have htwo : 2 ≤ u / ‖x‖ := (le_div_iff₀ hxpos).mpr hux
    linarith
  · calc
      ‖1 + (u : ℂ) / x‖ ≤ 1 + u / ‖x‖ := by
        simpa only [norm_one, hnorm] using norm_add_le (1 : ℂ) ((u : ℂ) / x)
      _ ≤ u + u / ‖x‖ := by linarith
      _ = (1 + ‖x‖⁻¹) * u := by ring

theorem regularizingBracket_polynomial_bound (r x : ℂ) (hx : x ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, max 1 (2 * ‖x‖) ≤ u →
      ‖regularizingBracket r x u‖ ≤ C * u ^ (max r.re 0) := by
  let a := max r.re 0
  let B := Real.exp (Real.pi * |r.im|) * (1 + ‖x‖⁻¹) ^ a
  refine ⟨B + 1, by dsimp [B]; positivity, ?_⟩
  intro u hu
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  have hxbound := norm_one_add_real_div_bounds x hx hu
  have hpow : ‖1 + (u : ℂ) / x‖ ^ a ≤ (1 + ‖x‖⁻¹) ^ a * u ^ a := by
    rw [← Real.mul_rpow (by positivity) hu0]
    exact Real.rpow_le_rpow (norm_nonneg _) hxbound.2 (le_max_right _ _)
  have hbig := norm_cpow_le_rpow_max (1 + (u : ℂ) / x) r hxbound.1
  have huPow : 1 ≤ u ^ a := Real.one_le_rpow hu1 (le_max_right _ _)
  calc
    ‖regularizingBracket r x u‖ ≤ ‖(1 + (u : ℂ) / x) ^ r‖ + 1 := by
      simpa only [regularizingBracket, norm_one] using
        norm_sub_le ((1 + (u : ℂ) / x) ^ r) 1
    _ ≤ Real.exp (Real.pi * |r.im|) *
        ((1 + ‖x‖⁻¹) ^ a * u ^ a) + u ^ a := by
      exact add_le_add (hbig.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)) huPow
    _ = (B + 1) * u ^ a := by dsimp [B]; ring

end DefocusingNLS

end OAI
