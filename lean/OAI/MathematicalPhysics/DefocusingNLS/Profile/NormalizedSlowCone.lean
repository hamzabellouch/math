import OAI.MathematicalPhysics.DefocusingNLS.Profile.NormalizedSlowTail

namespace OAI

/-! # Strict tail cone including the removable parameter -/

open Filter Topology

namespace DefocusingNLS

theorem normalizedSlow_tail_nontrivial (q : ℂ) (M K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hK : 0 < K) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    ∃ n, K ≤ n ∧ normalizedSlowCoefficient q (M + 1) s n ≠ 0 := by
  by_contra hn
  push Not at hn
  have hB (j : ℕ) : normalizedSlowB q (M + 1) s (j + K) = normalizedSlowB q (M + 1) s K := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [show j + 1 + K = (j + K) + 1 by omega, normalizedSlowB_succ,
          hn (j + K) (by omega), sub_zero, ih]
  have hBK : normalizedSlowB q (M + 1) s K = 0 := by
    have hl := (normalizedSlowB_tendsto_zero q (M + 1) s hq hsre hsim).comp
      (tendsto_add_atTop_nat K)
    have hc : Tendsto (fun j => normalizedSlowB q (M + 1) s (j + K)) atTop
        (𝓝 (normalizedSlowB q (M + 1) s K)) := by simpa only [hB] using tendsto_const_nhds
    exact tendsto_nhds_unique hc hl
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  have hq0 : q + 1 ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  obtain ⟨j, hj, hgj⟩ := slowLaguerre_tail_nontrivial (q + 1) (M + 1) K s hq' hq0 hK hsre hsim
  have hz := hB (j + 1 - K)
  rw [Nat.sub_add_cancel (by omega : K ≤ j + 1), hBK] at hz
  simp only [normalizedSlowB, Nat.add_sub_cancel] at hz
  exact hgj hz

theorem normalizedSlow_cone_increment (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hn : 1 ≤ n) (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    coneForm M s (normalizedSlowB q (M + 1) s (n + 1))
        (normalizedSlowC q (M + 1) s (n + 1)) -
      coneForm M s (normalizedSlowB q (M + 1) s n) (normalizedSlowC q (M + 1) s n) =
        (q.re + n - M / 2) * Complex.normSq (normalizedSlowCoefficient q (M + 1) s n) := by
  have h := normalizedSlow_recurrence q M s n hn hq hsre hsim
  rw [normalizedSlowB_succ q _ s n] at h
  have h' := coneForm_increment (M : ℝ) s (q + n)
    (normalizedSlowB q (M + 1) s n) (normalizedSlowC q (M + 1) s n)
    (normalizedSlowCoefficient q (M + 1) s n) hsre (by simpa using h)
  rw [normalizedSlowC_succ, normalizedSlowB_succ q _ s n]
  simpa only [Complex.add_re, Complex.natCast_re] using h'

theorem normalizedSlow_strict_cone (σ : ℝ) (ℓ K : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    coneForm ((ℓ : ℝ) + 5) s (normalizedSlowB q (ℓ + 6) s K)
      (normalizedSlowC q (ℓ + 6) s K) < 0 := by
  have hq' : -1 < q.re := by rw [hq]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  let P := fun n => coneForm ((ℓ : ℝ) + 5) s (normalizedSlowB q (ℓ + 6) s n)
    (normalizedSlowC q (ℓ + 6) s n)
  have hi (n : ℕ) (hn : 1 ≤ n) : P (n + 1) - P n =
      (σ + n - 5 / 2) * Complex.normSq (normalizedSlowCoefficient q (ℓ + 6) s n) := by
    have h := normalizedSlow_cone_increment q (ℓ + 5) s n hn hq' hsre hsim
    have he : ℓ + 5 + 1 = ℓ + 6 := by omega
    rw [he] at h
    push_cast at h
    rw [hq] at h
    convert h using 1
    ring
  apply negative_of_increasing_tail K
    (coneForm_tendsto_zero _ _ _ _
      (normalizedSlowB_tendsto_zero q (ℓ + 6) s hq' hsre hsim)
      (normalizedSlowC_tendsto_zero q (ℓ + 6) s hq' hsre hsim))
  · intro n hn
    have h := mode_increment_nonneg σ n (normalizedSlowCoefficient q (ℓ + 6) s n)
      hσ (hK.trans hn)
    linarith [hi n (by omega)]
  · obtain ⟨n, hn, hg⟩ := normalizedSlow_tail_nontrivial q (ℓ + 5) K s hq' (by omega) hsre hsim
    have he : ℓ + 5 + 1 = ℓ + 6 := by omega
    rw [he] at hg
    refine ⟨n, hn, ?_⟩
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hK.trans hn
    have hpos : 0 < (σ + n - 5 / 2) * Complex.normSq (normalizedSlowCoefficient q (ℓ + 6) s n) :=
      mul_pos (by linarith) (Complex.normSq_pos.mpr hg)
    linarith [hi n (by omega)]

/-- The tail denominator is nonzero and its ratio lies in the strict disk,
including at `q = 0`. -/
theorem normalizedSlow_tail_disk (σ : ℝ) (ℓ K : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    normalizedSlowC q (ℓ + 6) s K ≠ 0 ∧
      Complex.normSq (normalizedSlowB q (ℓ + 6) s K / normalizedSlowC q (ℓ + 6) s K +
        s / ((ℓ : ℝ) + 5 : ℂ)) < Complex.normSq (s / ((ℓ : ℝ) + 5 : ℂ)) := by
  have hM : 0 < (ℓ : ℝ) + 5 := by positivity
  have hc := normalizedSlow_strict_cone σ ℓ K q s hσ hK hq hsre hsim
  have hd := tail_disk_of_negative_cone ((ℓ : ℝ) + 5) s
    (normalizedSlowB q (ℓ + 6) s K) (normalizedSlowC q (ℓ + 6) s K) hM hc
  push_cast at hd
  exact hd

end DefocusingNLS

end OAI
