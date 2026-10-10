import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowJetUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingColumns

namespace OAI

/-! # Actual backward columns and the strict cone away from the removable parameter -/

open Filter Topology Matrix Polynomial

namespace DefocusingNLS

theorem slowLaguerre_backward_relation (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    (q + n - M) * slowLaguerreB q (M + 1) s (n + 1) =
      (q + n) * slowLaguerreB q (M + 1) s n + s * slowLaguerreC q (M + 1) s n := by
  have h := slowLaguerre_recurrence q M s n hq hsre hsim
  have hg : slowLaguerreCoefficient q (M + 1) s n =
      slowLaguerreB q (M + 1) s n - slowLaguerreB q (M + 1) s (n + 1) := by
    rw [slowLaguerreB_succ]
    ring
  rw [hg] at h
  linear_combination -h

theorem slowLaguerre_backwardProduct (q : ℂ) (M K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    backwardProduct M s q K *ᵥ
      ![slowLaguerreB q (M + 1) s K, slowLaguerreC q (M + 1) s K] =
      (ascPochhammer ℂ K).eval q •
        ![regularizedSlowSolution q (M + 1) (-s),
          -deriv (regularizedSlowSolution q (M + 1)) (-s)] := by
  simpa only [slowLaguerreB_zero, slowLaguerreC_zero] using
    backwardProduct_apply (M : ℂ) s q (slowLaguerreB q (M + 1) s)
      (slowLaguerreC q (M + 1) s)
      (fun n => slowLaguerre_backward_relation q M s n hq hsre hsim)
      (fun n => slowLaguerreC_succ q (M + 1) s n) K

theorem slowLaguerre_pair_nonzero (q : ℂ) (M K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hq0 : q ≠ 0) (hK : 0 < K)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    slowLaguerreB q (M + 1) s K ≠ 0 ∨ slowLaguerreC q (M + 1) s K ≠ 0 := by
  by_contra hn
  push Not at hn
  have hp : (ascPochhammer ℂ K).eval q ≠ 0 := by
    intro hz
    exact hq0 ((pochhammer_zero_iff q K hK hq).mp hz)
  have h := slowLaguerre_backwardProduct q M K s hq hsre hsim
  rw [hn.1, hn.2] at h
  have hv : ![(0 : ℂ), 0] = (0 : Fin 2 → ℂ) := by ext i; fin_cases i <;> rfl
  rw [hv, Matrix.mulVec_zero] at h
  have h0 := congrArg (fun v : Fin 2 → ℂ => v 0) h
  have h1 := congrArg (fun v : Fin 2 → ℂ => v 1) h
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  have hv0 := (mul_eq_zero.mp h0.symm).resolve_left hp
  have hv1 := neg_eq_zero.mp ((mul_eq_zero.mp h1.symm).resolve_left hp)
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => hsim (by simp [h]))
  have hj := regularizedSlowSolution_jet_nonzero q (M + 1) (-s) hq
    (by simp [hsre]) hs0
  exact hj.elim (fun h => h hv0) (fun h => h hv1)

theorem slowLaguerre_tail_nontrivial (q : ℂ) (M K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hq0 : q ≠ 0) (hK : 0 < K)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    ∃ n, K ≤ n ∧ slowLaguerreCoefficient q (M + 1) s n ≠ 0 := by
  by_contra hn
  push Not at hn
  have hB (j : ℕ) : slowLaguerreB q (M + 1) s (j + K) = slowLaguerreB q (M + 1) s K := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [show j + 1 + K = (j + K) + 1 by omega, slowLaguerreB_succ,
          hn (j + K) (by omega), sub_zero, ih]
  have hBK : slowLaguerreB q (M + 1) s K = 0 := by
    have hl := (slowLaguerreB_tendsto_zero q (M + 1) s hq hsre hsim).comp
      (tendsto_add_atTop_nat K)
    have hc : Tendsto (fun j => slowLaguerreB q (M + 1) s (j + K)) atTop
        (𝓝 (slowLaguerreB q (M + 1) s K)) := by simpa only [hB] using tendsto_const_nhds
    exact tendsto_nhds_unique hc hl
  have hC (j : ℕ) : slowLaguerreC q (M + 1) s (j + K) = slowLaguerreC q (M + 1) s K := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [show j + 1 + K = (j + K) + 1 by omega, slowLaguerreC_succ]
        rw [show j + K + 1 = (j + 1) + K by omega, hB, hBK, sub_zero, ih]
  have hCK : slowLaguerreC q (M + 1) s K = 0 := by
    have hl := (slowLaguerreC_tendsto_zero q (M + 1) s hq hsre hsim).comp
      (tendsto_add_atTop_nat K)
    have hc : Tendsto (fun j => slowLaguerreC q (M + 1) s (j + K)) atTop
        (𝓝 (slowLaguerreC q (M + 1) s K)) := by simpa only [hC] using tendsto_const_nhds
    exact tendsto_nhds_unique hc hl
  exact (slowLaguerre_pair_nonzero q M K s hq hq0 hK hsre hsim).elim
    (fun h => h hBK) (fun h => h hCK)

theorem slowLaguerre_strict_cone (σ : ℝ) (ℓ K : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hq0 : q ≠ 0)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    coneForm ((ℓ : ℝ) + 5) s (slowLaguerreB q (ℓ + 6) s K)
      (slowLaguerreC q (ℓ + 6) s K) < 0 := by
  have hq' : -1 < q.re := by rw [hq]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  let P := fun n => coneForm ((ℓ : ℝ) + 5) s (slowLaguerreB q (ℓ + 6) s n)
    (slowLaguerreC q (ℓ + 6) s n)
  have hi (n : ℕ) : P (n + 1) - P n =
      (σ + n - 5 / 2) * Complex.normSq (slowLaguerreCoefficient q (ℓ + 6) s n) :=
    slowLaguerre_mode_cone_increment σ ℓ n q s hσ hq hsre hsim
  apply negative_of_increasing_tail K
    (coneForm_tendsto_zero _ _ _ _
      (slowLaguerreB_tendsto_zero q (ℓ + 6) s hq' hsre hsim)
      (slowLaguerreC_tendsto_zero q (ℓ + 6) s hq' hsre hsim))
  · intro n hn
    have h := mode_increment_nonneg σ n (slowLaguerreCoefficient q (ℓ + 6) s n)
      hσ (hK.trans hn)
    linarith [hi n]
  · obtain ⟨n, hn, hg⟩ := slowLaguerre_tail_nontrivial q (ℓ + 5) K s hq' hq0
      (by omega) hsre hsim
    have he : ℓ + 5 + 1 = ℓ + 6 := by omega
    rw [he] at hg
    refine ⟨n, hn, ?_⟩
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hK.trans hn
    have hpos : 0 < (σ + n - 5 / 2) * Complex.normSq (slowLaguerreCoefficient q (ℓ + 6) s n) :=
      mul_pos (by linarith) (Complex.normSq_pos.mpr hg)
    linarith [hi n]

end DefocusingNLS

end OAI
