import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

namespace Alternating
open scoped Topology

noncomputable def clock (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

theorem clock_smooth : ContDiff ℝ (⊤ : ℕ∞) clock := by unfold clock; fun_prop

theorem clock_zero {t : ℝ} (ht : t ≤ 1 / 4) : clock t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem clock_one {t : ℝ} (ht : 3 / 4 ≤ t) : clock t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem clock_mem (t : ℝ) : clock t ∈ Set.Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem clock_monotone : Monotone clock := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)

theorem clock_deriv_nonneg (t : ℝ) : 0 ≤ deriv clock t := clock_monotone.deriv_nonneg

theorem clock_deriv_collar (n : ℕ) {t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    iteratedDeriv (n + 1) clock t = 0 := by
  rcases ht with ht | ht
  · have he : clock =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact clock_zero hs.le
    simpa [iteratedDeriv_const] using he.iteratedDeriv_eq (n + 1)
  · have he : clock =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact clock_one hs.le
    simpa [iteratedDeriv_const] using he.iteratedDeriv_eq (n + 1)

theorem clock_deriv_support (n : ℕ) :
    tsupport (iteratedDeriv (n + 1) clock) ⊆ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have hor : t < 1 / 4 ∨ 3 / 4 < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hn
  exact ht (clock_deriv_collar n hor)

theorem clock_deriv_compact (n : ℕ) : HasCompactSupport (iteratedDeriv (n + 1) clock) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (clock_deriv_support n)

theorem clock_derivatives_bounded (n : ℕ) : ∃ M : ℝ, 0 < M ∧
    ∀ t : ℝ, |iteratedDeriv n clock t| ≤ M := by
  cases n with
  | zero =>
    exact ⟨1, by norm_num, fun t => by simpa [abs_of_nonneg (clock_mem t).1] using (clock_mem t).2⟩
  | succ n =>
    have hc := clock_smooth.continuous_iteratedDeriv (n + 1)
      (by exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))
    obtain ⟨M, hM, hbound⟩ := ((clock_deriv_compact n).isCompact_range hc).isBounded.exists_pos_norm_le
    exact ⟨M, hM, fun t => by simpa using hbound _ ⟨t, rfl⟩⟩

theorem clock_total_progress : ∫ t : ℝ in (0 : ℝ)..1, deriv clock t = 1 := by
  have hc := clock_smooth.continuous_deriv (by norm_num)
  rw [intervalIntegral.integral_deriv_eq_sub' clock rfl
    (fun x _ => clock_smooth.differentiable (by norm_num) x) hc.continuousOn]
  rw [clock_one (by norm_num), clock_zero (by norm_num)]
  norm_num

end Alternating

end OAI
