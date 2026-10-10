import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowMatchingColumns

namespace OAI

/-! # A nonsingular normalization of the slow tail

The only vanishing Pochhammer factor in the relevant half-plane is `q`.
Coefficients of `H(q+1,m+1)` give the tail divided by this factor without
division. The resulting recurrence remains meaningful at `q = 0`.
-/

open Filter Topology

namespace DefocusingNLS

noncomputable def normalizedSlowB (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  slowLaguerreCoefficient (q + 1) (m + 1) s (n - 1)

noncomputable def normalizedSlowC (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  slowLaguerreB (q + 1) (m + 1) s n

noncomputable def normalizedSlowCoefficient (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  slowLaguerreCoefficient (q + 1) (m + 1) s (n - 1) -
    slowLaguerreCoefficient (q + 1) (m + 1) s n

theorem normalizedSlowB_succ (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) :
    normalizedSlowB q m s (n + 1) =
      normalizedSlowB q m s n - normalizedSlowCoefficient q m s n := by
  simp only [normalizedSlowB, normalizedSlowCoefficient, Nat.add_sub_cancel]
  ring

theorem normalizedSlowC_succ (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) :
    normalizedSlowC q m s (n + 1) = normalizedSlowC q m s n - normalizedSlowB q m s (n + 1) := by
  simp only [normalizedSlowC, normalizedSlowB, Nat.add_sub_cancel, slowLaguerreB_succ]

/-- The normalized recurrence holds at the removable parameter `q = 0`. -/
theorem normalizedSlow_recurrence_succ (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    (q + (n + 1 : ℕ)) * normalizedSlowCoefficient q (M + 1) s (n + 1) =
      -(M : ℂ) * normalizedSlowB q (M + 1) s (n + 2) -
        s * normalizedSlowC q (M + 1) s (n + 1) := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  have h0 := slowLaguerre_recurrence (q + 1) (M + 1) s n hq' hsre hsim
  have h1 := slowLaguerre_recurrence (q + 1) (M + 1) s (n + 1) hq' hsre hsim
  rw [slowLaguerreB_succ, slowLaguerreC_succ] at h1
  simp only [normalizedSlowCoefficient, normalizedSlowB, normalizedSlowC,
    Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega]
  push_cast at h0 h1 ⊢
  linear_combination h0 - h1

theorem normalizedSlow_recurrence (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hn : 1 ≤ n) (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    (q + n) * normalizedSlowCoefficient q (M + 1) s n =
      -(M : ℂ) * normalizedSlowB q (M + 1) s (n + 1) -
        s * normalizedSlowC q (M + 1) s n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa only [add_comm, add_left_comm, add_assoc] using
    normalizedSlow_recurrence_succ q M s j hq hsre hsim

theorem normalizedSlowB_tendsto_zero (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    Tendsto (normalizedSlowB q m s) atTop (𝓝 0) := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  exact (shiftedSlowDerivative_laguerre_tendsto_zero 0 (q + 1) (m + 1) s hq' hsre hsim).comp
    (tendsto_sub_atTop_nat 1)

theorem normalizedSlowC_tendsto_zero (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    Tendsto (normalizedSlowC q m s) atTop (𝓝 0) := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  exact slowLaguerreB_tendsto_zero (q + 1) (m + 1) s hq' hsre hsim

end DefocusingNLS

end OAI
