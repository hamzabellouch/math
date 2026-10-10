import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryHermitianPolynomial

namespace OAI

/-! # Structural cancellation in the boundary determinant

The proof holds for every coherent choice of constant terms. It never uses
cancellation observed at the certificate's central parameter values.
-/

open Polynomial Matrix

namespace DefocusingNLS

noncomputable def boundaryLeadingMatrix (K : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I ^ K, 0; -(K : ℂ) * Complex.I ^ K, Complex.I ^ K]

theorem boundaryForwardProduct_top_matrix (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ) :
    (fun i j => (boundaryForwardProduct M s a K i j).coeff K) = boundaryLeadingMatrix K := by
  have h := boundaryForwardProduct_top M s a K
  ext i j
  fin_cases i <;> fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem star_I_pow_mul (K : ℕ) : star (Complex.I ^ K) * Complex.I ^ K = 1 := by
  rw [star_pow, ← mul_pow]
  simp

theorem forwardFormEntry_boundaryLeadingMatrix (M : ℝ) (s : ℂ) (K : ℕ) (i j : Fin 2) :
    forwardFormEntry M s (boundaryLeadingMatrix K) i j =
      (!![(M : ℂ), s; -s, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  have h := star_I_pow_mul K
  have hK : star (K : ℂ) = (K : ℂ) := by simp
  fin_cases i <;> fin_cases j
  · change (M : ℂ) * star (Complex.I ^ K) * Complex.I ^ K +
      s * (star (Complex.I ^ K) * (-(K : ℂ) * Complex.I ^ K) -
        star (-(K : ℂ) * Complex.I ^ K) * Complex.I ^ K) = M
    simp only [star_mul, star_neg, hK]
    linear_combination (M : ℂ) * h
  · change (M : ℂ) * star (Complex.I ^ K) * 0 +
      s * (star (Complex.I ^ K) * Complex.I ^ K -
        star (-(K : ℂ) * Complex.I ^ K) * 0) = s
    simp only [mul_zero, sub_zero, zero_add]
    rw [h, mul_one]
  · change (M : ℂ) * star (0 : ℂ) * Complex.I ^ K +
      s * (star (0 : ℂ) * (-(K : ℂ) * Complex.I ^ K) -
        star (Complex.I ^ K) * Complex.I ^ K) = -s
    simp only [star_zero, mul_zero, zero_mul, zero_add, zero_sub, h, mul_neg_one]
  · change (M : ℂ) * star (0 : ℂ) * 0 +
      s * (star (0 : ℂ) * Complex.I ^ K - star (Complex.I ^ K) * 0) = 0
    simp

theorem boundaryHermitian_top (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ) (i j : Fin 2) :
    (hermitianPolynomial M s (boundaryForwardProduct M s a K) i j).coeff (2 * K) =
      (!![(M : ℂ), s; -s, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  rw [hermitianPolynomial_top M s _ K (boundaryForwardProduct_degree M s a K),
    boundaryForwardProduct_top_matrix, forwardFormEntry_boundaryLeadingMatrix]

theorem boundaryReflected_top (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ)
    (hs : s.re = 0) (i j : Fin 2) :
    (reflectedHermitianPolynomial M s (boundaryForwardProduct M s a K) i j).coeff (2 * K) =
      (!![((2 * M : ℝ) : ℂ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  rw [reflectedHermitianPolynomial_coefficient, boundaryHermitian_top]
  have he : (-1 : ℂ) ^ (2 * K) = 1 := by rw [pow_mul]; simp
  have hM : star (M : ℂ) = (M : ℂ) := Complex.conj_ofReal M
  fin_cases i <;> fin_cases j <;>
    simp [he, hM, star_eq_neg_of_re_zero s hs]
  ring

theorem conjugatePolynomial_add (p q : Polynomial ℂ) :
    conjugatePolynomial (p + q) = conjugatePolynomial p + conjugatePolynomial q := by
  simp [conjugatePolynomial]

theorem conjugatePolynomial_sub (p q : Polynomial ℂ) :
    conjugatePolynomial (p - q) = conjugatePolynomial p - conjugatePolynomial q := by
  simp [conjugatePolynomial]

theorem conjugatePolynomial_mul (p q : Polynomial ℂ) :
    conjugatePolynomial (p * q) = conjugatePolynomial p * conjugatePolynomial q := by
  simp [conjugatePolynomial]

theorem conjugatePolynomial_C (z : ℂ) : conjugatePolynomial (C z) = C (star z) := by
  simp [conjugatePolynomial]

theorem conjugatePolynomial_conjugate (p : Polynomial ℂ) :
    conjugatePolynomial (conjugatePolynomial p) = p := by
  ext n
  simp only [coeff_conjugatePolynomial, star_star]

theorem hermitianPolynomial_conjugate (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (hs : s.re = 0) (i j : Fin 2) :
    conjugatePolynomial (hermitianPolynomial M s T j i) = hermitianPolynomial M s T i j := by
  have hM : star (M : ℂ) = (M : ℂ) := Complex.conj_ofReal M
  simp only [hermitianPolynomial, conjugatePolynomial_add, conjugatePolynomial_mul,
    conjugatePolynomial_sub, conjugatePolynomial_C, conjugatePolynomial_conjugate,
    hM, star_eq_neg_of_re_zero s hs, map_neg]
  ring

theorem hermitianPolynomial_diagonal_coefficient (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (hs : s.re = 0) (i : Fin 2) (n : ℕ) :
    star ((hermitianPolynomial M s T i i).coeff n) =
      (hermitianPolynomial M s T i i).coeff n := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff n)
    (hermitianPolynomial_conjugate M s T hs i i)
  simpa only [coeff_conjugatePolynomial] using h

theorem reflectedHermitianPolynomial_diagonal_odd (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (hs : s.re = 0) (i : Fin 2) (n : ℕ)
    (hn : Odd n) : (reflectedHermitianPolynomial M s T i i).coeff n = 0 := by
  rw [reflectedHermitianPolynomial_coefficient,
    hermitianPolynomial_diagonal_coefficient M s T hs, hn.neg_one_pow]
  ring

theorem boundaryReflected_offDiagonal_degree (M : ℝ) (s : ℂ) (a : ℕ → ℂ)
    (K : ℕ) (hK : 0 < K) (hs : s.re = 0) :
    (reflectedHermitianPolynomial M s (boundaryForwardProduct M s a K) 0 1).natDegree ≤ 2 * K - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases he : n = 2 * K
  · subst n
    exact boundaryReflected_top M s a K hs 0 1
  · exact coeff_eq_zero_of_natDegree_lt
      ((reflectedHermitianPolynomial_degree M s _ K (boundaryForwardProduct_degree M s a K) 0 1).trans_lt
        (by omega))

theorem boundaryReflected_secondDiagonal_degree (M : ℝ) (s : ℂ) (a : ℕ → ℂ)
    (K : ℕ) (hK : 0 < K) (hs : s.re = 0) :
    (reflectedHermitianPolynomial M s (boundaryForwardProduct M s a K) 1 1).natDegree ≤ 2 * K - 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases he : n = 2 * K
  · subst n
    exact boundaryReflected_top M s a K hs 1 1
  by_cases ho : n = 2 * K - 1
  · apply reflectedHermitianPolynomial_diagonal_odd M s _ hs 1 n
    exact ⟨K - 1, by omega⟩
  · exact coeff_eq_zero_of_natDegree_lt
      ((reflectedHermitianPolynomial_degree M s _ K (boundaryForwardProduct_degree M s a K) 1 1).trans_lt
        (by omega))

noncomputable def boundaryDeterminantPolynomial (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ) : Polynomial ℂ :=
  let S := reflectedHermitianPolynomial M s (boundaryForwardProduct M s a K)
  S 0 0 * S 1 1 - S 0 1 * conjugatePolynomial (S 0 1)

/-- The cancellation required by the finite certificate is uniform throughout
its parameter box: at depth eight the determinant has degree at most thirty. -/
theorem boundaryDeterminantPolynomial_degree (M : ℝ) (s : ℂ) (a : ℕ → ℂ)
    (K : ℕ) (hK : 0 < K) (hs : s.re = 0) :
    (boundaryDeterminantPolynomial M s a K).natDegree ≤ 4 * K - 2 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans ((add_le_add
      (reflectedHermitianPolynomial_degree M s _ K (boundaryForwardProduct_degree M s a K) 0 0)
      (boundaryReflected_secondDiagonal_degree M s a K hK hs)).trans (by omega))
  · exact natDegree_mul_le.trans ((add_le_add
      (boundaryReflected_offDiagonal_degree M s a K hK hs)
      ((conjugatePolynomial_degree _).trans
        (boundaryReflected_offDiagonal_degree M s a K hK hs))).trans (by omega))

end DefocusingNLS

end OAI
