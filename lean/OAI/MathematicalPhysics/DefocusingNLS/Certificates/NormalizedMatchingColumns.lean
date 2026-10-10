import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAdjacentParameter

namespace OAI

/-! # The normalized backward column, including the removable parameter -/

open Matrix Polynomial

namespace DefocusingNLS

theorem normalizedSlowC_one (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    normalizedSlowC q m s 1 = regularizedSlowSolution (q + 1) (m + 1) (-s) -
      regularizedSlowSolution (q + 1) m (-s) := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  change slowLaguerreB (q + 1) (m + 1) s (0 + 1) = _
  rw [slowLaguerreB_succ, slowLaguerreB_zero,
    slowLaguerreCoefficient_zero (q + 1) m s hq' hsre hsim]

theorem normalizedSlow_initial_column (q : ℂ) (M : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    backwardMatrix M s q *ᵥ ![normalizedSlowB q (M + 1) s 1,
      normalizedSlowC q (M + 1) s 1] =
        ![regularizedSlowSolution q (M + 1) (-s),
          -deriv (regularizedSlowSolution q (M + 1)) (-s)] := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => hsim (by simp [h]))
  have hx : 0 ≤ (-s).re := by simp [hsre]
  have hc := regularizedSlowSolution_contiguous q (M + 1) (-s) hq hx hs0
  have hd := (hasDerivAt_regularizedSlowSolution_shift_closed q (M + 1) (-s) hq hx hs0).deriv
  rw [normalizedSlowB_one q (M + 1) s hq hsre hsim,
    normalizedSlowC_one q (M + 1) s hq hsre hsim]
  ext i
  fin_cases i
  · simp [backwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
    linear_combination -hc
  · simp [backwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    ring

theorem normalizedSlow_backward_relation (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hn : 1 ≤ n) (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    (q + n - M) * normalizedSlowB q (M + 1) s (n + 1) =
      (q + n) * normalizedSlowB q (M + 1) s n +
        s * normalizedSlowC q (M + 1) s n := by
  have h := normalizedSlow_recurrence q M s n hn hq hsre hsim
  have hg : normalizedSlowCoefficient q (M + 1) s n =
      normalizedSlowB q (M + 1) s n - normalizedSlowB q (M + 1) s (n + 1) := by
    rw [normalizedSlowB_succ]
    ring
  rw [hg] at h
  linear_combination -h

/-- The factor q has disappeared from the backward product, with no division
in the argument. In particular this formula is valid at q=0. -/
theorem normalizedSlow_backwardProduct (q : ℂ) (M K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    backwardProduct M s q (K + 1) *ᵥ
      ![normalizedSlowB q (M + 1) s (K + 1), normalizedSlowC q (M + 1) s (K + 1)] =
      (ascPochhammer ℂ K).eval (q + 1) •
        ![regularizedSlowSolution q (M + 1) (-s),
          -deriv (regularizedSlowSolution q (M + 1)) (-s)] := by
  induction K with
  | zero =>
      simpa only [backwardProduct, Matrix.one_mul, Nat.cast_zero, add_zero,
        ascPochhammer_zero, Polynomial.eval_one, one_smul] using
        normalizedSlow_initial_column q M s hq hsre hsim
  | succ K ih =>
      rw [backwardProduct, ← Matrix.mulVec_mulVec,
        backwardMatrix_step M s (q + (K + 1 : ℕ)) _ _ _ _
          (normalizedSlow_backward_relation q M s (K + 1) (by omega) hq hsre hsim)
          (normalizedSlowC_succ q (M + 1) s (K + 1)),
        Matrix.mulVec_smul, ih, smul_smul, ascPochhammer_succ_eval]
      congr 1
      push_cast
      ring

theorem shiftedPochhammer_ne_zero (q : ℂ) (K : ℕ) (hq : -1 < q.re) :
    (ascPochhammer ℂ K).eval (q + 1) ≠ 0 := by
  intro hz
  obtain ⟨n, _, hn⟩ := (ascPochhammer_eval_eq_zero_iff K (q + 1)).mp hz
  have hre := congrArg Complex.re hn
  simp only [Complex.natCast_re, Complex.neg_re, Complex.add_re, Complex.one_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) n]

noncomputable def normalizedMatchingB (q : ℂ) (m : ℕ) (s : ℂ) (K : ℕ) : ℂ :=
  normalizedSlowB q m s K / (ascPochhammer ℂ (K - 1)).eval (q + 1)

noncomputable def normalizedMatchingC (q : ℂ) (m : ℕ) (s : ℂ) (K : ℕ) : ℂ :=
  normalizedSlowC q m s K / (ascPochhammer ℂ (K - 1)).eval (q + 1)

/-- The fully normalized tail produces precisely the actual boundary jet. -/
theorem normalizedMatching_backwardProduct (q : ℂ) (M K : ℕ) (s : ℂ)
    (hK : 0 < K) (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    backwardProduct M s q K *ᵥ
      ![normalizedMatchingB q (M + 1) s K, normalizedMatchingC q (M + 1) s K] =
        ![regularizedSlowSolution q (M + 1) (-s),
          -deriv (regularizedSlowSolution q (M + 1)) (-s)] := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hp := shiftedPochhammer_ne_zero q j hq
  have hv : ![normalizedMatchingB q (M + 1) s (j + 1),
      normalizedMatchingC q (M + 1) s (j + 1)] =
      ((ascPochhammer ℂ j).eval (q + 1))⁻¹ •
        ![normalizedSlowB q (M + 1) s (j + 1), normalizedSlowC q (M + 1) s (j + 1)] := by
    ext i
    fin_cases i <;> simp [normalizedMatchingB, normalizedMatchingC, div_eq_mul_inv, mul_comm]
  rw [hv, Matrix.mulVec_smul, normalizedSlow_backwardProduct q M j s hq hsre hsim,
    smul_smul, inv_mul_cancel₀ hp, one_smul]

end DefocusingNLS

end OAI
