import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeSecondBound

namespace OAI

/-! # Uniform second-logarithmic-derivative control inside a zero-free disk -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem deriv_logDeriv_norm_le_inner_disk (g : ℂ → ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ R / 4) :
    ‖deriv (logDeriv g) w‖ ≤ 64 * A / R ^ 2 := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hquarter : 0 < R / 4 := by positivity
  have hsmall (z : ℂ) (hz : z ∈ closedBall w (R / 4)) : ‖z‖ ≤ R / 2 := by
    have hz' : ‖z - w‖ ≤ R / 4 := mem_closedBall_iff_norm.mp hz
    have ht := norm_add_le (z - w) w
    rw [sub_add_cancel] at ht
    linarith
  have hin (z : ℂ) (hz : z ∈ closedBall w (R / 4)) : z ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right] using (hsmall z hz).trans_lt (by linarith : R / 2 < R)
  have hdc : DiffContOnCl ℂ F (ball w (R / 4)) := by
    refine ⟨fun z hz => (hF z (hin z (ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt, ?_⟩
    rw [closure_ball w hquarter.ne']
    exact fun z hz => (hF z (hin z hz)).continuousAt.continuousWithinAt
  have hb : ∀ z ∈ sphere w (R / 4), ‖F z‖ ≤ 2 * A := by
    intro z hz
    have hz' := sphere_subset_closedBall hz
    have hn := hsmall z hz'
    have hh := Complex.borelCaratheodory_zero hA hd hreal hR (hin z hz') hF0
    apply hh.trans
    have hden : 0 < R - ‖z‖ := by linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hwball : w ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using hw.trans_lt (by linarith : R / 4 < R)
  have he : deriv F =ᶠ[𝓝 w] logDeriv g := by
    filter_upwards [isOpen_ball.mem_nhds hwball] with z hz
    exact (hF z hz).deriv
  have he' : iteratedDeriv 2 F w = deriv (logDeriv g) w := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he.deriv_eq
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hquarter hdc hb
  rw [he'] at hh
  convert hh using 1
  norm_num
  field_simp
  ring

end Ostmann

end OAI
