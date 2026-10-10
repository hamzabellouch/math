import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeDiskBound

namespace OAI

/-! # A second-derivative estimate for the normalized analytic logarithm -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem deriv_logDeriv_norm_le_of_disk (g : ℂ → ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A) :
    ‖deriv (logDeriv g) 0‖ ≤ 16 * A / R ^ 2 := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hhalf : 0 < R / 2 := by positivity
  have hsmall (z : ℂ) (hz : z ∈ closedBall 0 (R / 2)) : z ∈ ball 0 R :=
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hdc : DiffContOnCl ℂ F (ball 0 (R / 2)) := by
    refine ⟨hd.mono (ball_subset_ball (by linarith)), ?_⟩
    rw [closure_ball 0 hhalf.ne']
    exact fun z hz => (hF z (hsmall z hz)).continuousAt.continuousWithinAt
  have hb : ∀ z ∈ sphere 0 (R / 2), ‖F z‖ ≤ 2 * A := by
    intro z hz
    have hn : ‖z‖ = R / 2 := by simpa using hz
    have hh := Complex.borelCaratheodory_zero hA hd hreal hR
      (hsmall z (sphere_subset_closedBall hz)) hF0
    rw [hn] at hh
    convert hh using 1
    field_simp
    ring
  have he : deriv F =ᶠ[𝓝 (0 : ℂ)] logDeriv g := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    exact (hF z hz).deriv
  have he' : iteratedDeriv 2 F 0 = deriv (logDeriv g) 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he.deriv_eq
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hhalf hdc hb
  rw [he'] at hh
  convert hh using 1
  norm_num
  field_simp
  ring

end Ostmann

end OAI
