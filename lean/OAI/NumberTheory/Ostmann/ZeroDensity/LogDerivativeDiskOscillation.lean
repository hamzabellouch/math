import Mathlib.Analysis.Calculus.MeanValue
import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeInnerSecondBound

namespace OAI

/-! # Vanishing oscillation of logarithmic derivatives on inner disks -/

namespace Ostmann

open Complex Metric Set

theorem logDeriv_disk_oscillation (g : ℂ → ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (x y : ℂ) (hx : ‖x‖ ≤ R / 4) (hy : ‖y‖ ≤ R / 4) :
    ‖logDeriv g y - logDeriv g x‖ ≤ (64 * A / R ^ 2) * ‖y - x‖ := by
  have hin (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (R / 4)) : z ∈ ball 0 R := by
    have hz' : ‖z‖ ≤ R / 4 := by simpa using hz
    simpa only [mem_ball, dist_zero_right] using hz'.trans_lt (by linarith : R / 4 < R)
  have hd (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (R / 4)) :
      DifferentiableAt ℂ (logDeriv g) z :=
    ((hg z (hin z hz)).deriv.div (hg z (hin z hz)) (hne z (hin z hz))).differentiableAt
  apply (convex_closedBall (0 : ℂ) (R / 4)).norm_image_sub_le_of_norm_deriv_le hd
  · intro z hz
    exact deriv_logDeriv_norm_le_inner_disk g R A hR hA hg hne hlog z (by simpa using hz)
  · simpa using hx
  · simpa using hy

end Ostmann

end OAI
