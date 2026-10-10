import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeDiskBound

namespace OAI

/-! # A fixed small-disk logarithmic-derivative estimate -/

namespace Ostmann

open Complex Metric Set

theorem logDeriv_norm_le_small_disk (g : ℂ → ℂ) (A : ℝ) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 (3 / 2)))
    (hne : ∀ z ∈ ball 0 (3 / 2), g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 (3 / 2), Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖logDeriv g w‖ ≤ 48 * A := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g (3 / 2)
    (by norm_num) hg hne
  have hd : DifferentiableOn ℂ F (ball 0 (3 / 2)) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 (3 / 2)) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self (by norm_num))) (heF z hz)]
    exact hlog z hz
  have hv (v : ℂ) (hv : v ∈ closedBall w (1 / 8)) : ‖v‖ ≤ 9 / 8 := by
    have hh := norm_le_norm_sub_add v w
    have hdist : ‖v - w‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    linarith
  have hvball (v : ℂ) (h : v ∈ closedBall w (1 / 8)) : v ∈ ball 0 (3 / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith [hv v h]
  have hdc : DiffContOnCl ℂ F (ball w (1 / 8)) := by
    apply DiffContOnCl.mk_ball
    · intro v hv'
      exact (hF v (hvball v (ball_subset_closedBall hv'))).differentiableAt.differentiableWithinAt
    · exact fun v hv' => (hF v (hvball v hv')).continuousAt.continuousWithinAt
  have hbound : ∀ v ∈ sphere w (1 / 8), ‖F v‖ ≤ 6 * A := by
    intro v hv'
    have hvC := sphere_subset_closedBall hv'
    have hnv := hv v hvC
    have hden : 0 < 3 / 2 - ‖v‖ := by linarith
    have hh := Complex.borelCaratheodory_zero hA hd hreal (by norm_num)
      (hvball v hvC) hF0
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 8) hdc hbound
  have hwball : w ∈ ball 0 (3 / 2) := by rw [mem_ball, dist_zero_right]; linarith
  rw [(hF w hwball).deriv] at hh
  convert hh using 1
  ring

theorem logDeriv_norm_le_five_quarters_disk (g : ℂ → ℂ) (A : ℝ) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 (3 / 2)))
    (hne : ∀ z ∈ ball 0 (3 / 2), g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 (3 / 2), Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ 5 / 4) : ‖logDeriv g w‖ ≤ 352 * A := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g (3 / 2)
    (by norm_num) hg hne
  have hd : DifferentiableOn ℂ F (ball 0 (3 / 2)) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 (3 / 2)) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self (by norm_num))) (heF z hz)]
    exact hlog z hz
  have hv (v : ℂ) (hv : v ∈ closedBall w (1 / 16)) : ‖v‖ ≤ 21 / 16 := by
    have hh := norm_le_norm_sub_add v w
    have hdist : ‖v - w‖ ≤ 1 / 16 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    linarith
  have hvball (v : ℂ) (h : v ∈ closedBall w (1 / 16)) : v ∈ ball 0 (3 / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith [hv v h]
  have hdc : DiffContOnCl ℂ F (ball w (1 / 16)) := by
    apply DiffContOnCl.mk_ball
    · intro v hv'
      exact (hF v (hvball v (ball_subset_closedBall hv'))).differentiableAt.differentiableWithinAt
    · exact fun v hv' => (hF v (hvball v hv')).continuousAt.continuousWithinAt
  have hbound : ∀ v ∈ sphere w (1 / 16), ‖F v‖ ≤ 22 * A := by
    intro v hv'
    have hvC := sphere_subset_closedBall hv'
    have hnv := hv v hvC
    have hden : 0 < 3 / 2 - ‖v‖ := by linarith
    have hh := Complex.borelCaratheodory_zero hA hd hreal (by norm_num)
      (hvball v hvC) hF0
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 16) hdc hbound
  have hwball : w ∈ ball 0 (3 / 2) := by rw [mem_ball, dist_zero_right]; linarith
  rw [(hF w hwball).deriv] at hh
  convert hh using 1
  ring

end Ostmann

end OAI
