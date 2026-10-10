import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.LogDeriv

namespace OAI

/-! # A normalized logarithm on a zero-free disk

This is the local analytic bridge used to bound logarithmic derivatives on
zero-free disks. It is obtained by integrating the actual logarithmic derivative.
-/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem exists_normalized_log_on_ball (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0) :
    ∃ F : ℂ → ℂ, F 0 = 0 ∧ (∀ z ∈ ball 0 R, HasDerivAt F (logDeriv g z) z) ∧
      ∀ z ∈ ball 0 R, g z = g 0 * exp (F z) := by
  have hd : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    exact ((hg z hz).deriv.div (hg z hz) (hne z hz)).differentiableWithinAt
  obtain ⟨F, hF0, hF⟩ := hd.isExactOn_ball.with_val_at 0 0
  refine ⟨F, hF0, hF, ?_⟩
  let H : ℂ → ℂ := fun z => g z * exp (-F z)
  have hH (z : ℂ) (hz : z ∈ ball 0 R) : HasDerivAt H 0 z := by
    have h := (hg z hz).differentiableAt.hasDerivAt.mul ((hF z hz).neg.cexp)
    convert h using 1
    dsimp only [logDeriv_apply]
    field_simp [hne z hz]
    ring
  have hHD : DifferentiableOn ℂ H (ball 0 R) := fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  intro z hz
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
    hHD (fun w hw => (hH w hw).deriv) hz (mem_ball_self hR)
  change g z * exp (-F z) = g 0 * exp (-F 0) at hc
  rw [hF0, neg_zero, exp_zero, mul_one, exp_neg] at hc
  have hmul := congrArg (fun w : ℂ => w * exp (F z)) hc
  simpa [mul_assoc, exp_ne_zero] using hmul

theorem normalized_log_re (g F : ℂ → ℂ) (z : ℂ) (hg0 : g 0 ≠ 0)
    (he : g z = g 0 * exp (F z)) :
    (F z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
  have hnorm := congrArg norm he
  rw [norm_mul, norm_exp] at hnorm
  have hh := congrArg Real.log hnorm
  rw [Real.log_mul (norm_ne_zero_iff.mpr hg0) (Real.exp_ne_zero _), Real.log_exp] at hh
  linarith

end Ostmann

end OAI
