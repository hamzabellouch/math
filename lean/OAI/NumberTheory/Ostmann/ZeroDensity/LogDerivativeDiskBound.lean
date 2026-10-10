import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import OAI.NumberTheory.Ostmann.ZeroDensity.AnalyticLogBall

namespace OAI

/-! # A logarithmic-derivative estimate from the actual modulus on a disk -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem logDeriv_norm_le_of_disk (g : ℂ → ℂ) (R A : ℝ) (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A) :
    ‖logDeriv g 0‖ ≤ 4 * A / R := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hhalf : 0 < R / 2 := by positivity
  have hsmall (z : ℂ) (hz : z ∈ closedBall 0 (R / 2)) : z ∈ ball 0 R := by
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
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
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf hdc hb
  rw [(hF 0 (mem_ball_self hR)).deriv] at hh
  convert hh using 1
  field_simp
  ring

/-- The same modulus information controls the logarithmic derivative throughout
an inner half-disk, with the normalization still taken at its original center. -/
theorem logDeriv_norm_le_inner_disk (g : ℂ → ℂ) (R A : ℝ) (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ R / 2) : ‖logDeriv g w‖ ≤ 24 * A / R := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hv (v : ℂ) (hv : v ∈ closedBall w (R / 4)) : ‖v‖ ≤ 3 * R / 4 := by
    have hh := norm_le_norm_sub_add v w
    have hdist : ‖v - w‖ ≤ R / 4 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    linarith
  have hvball (v : ℂ) (h : v ∈ closedBall w (R / 4)) : v ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    linarith [hv v h]
  have hdc : DiffContOnCl ℂ F (ball w (R / 4)) := by
    apply DiffContOnCl.mk_ball
    · intro v hv'
      exact (hF v (hvball v (ball_subset_closedBall hv'))).differentiableAt.differentiableWithinAt
    · exact fun v hv' => (hF v (hvball v hv')).continuousAt.continuousWithinAt
  have hbound : ∀ v ∈ sphere w (R / 4), ‖F v‖ ≤ 6 * A := by
    intro v hv'
    have hvC := sphere_subset_closedBall hv'
    have hnv := hv v hvC
    have hden : 0 < R - ‖v‖ := by linarith
    have hh := Complex.borelCaratheodory_zero hA hd hreal hR (hvball v hvC) hF0
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < R / 4) hdc hbound
  have hwball : w ∈ ball 0 R := by rw [mem_ball, dist_zero_right]; linarith
  rw [(hF w hwball).deriv] at hh
  convert hh using 1
  field_simp
  ring

end Ostmann

end OAI
