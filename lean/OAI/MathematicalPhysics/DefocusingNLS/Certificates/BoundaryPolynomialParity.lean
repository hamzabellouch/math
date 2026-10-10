import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryPolynomialDegree

namespace OAI

/-! # Reality and evenness of the coherent boundary determinant -/

open Polynomial

namespace DefocusingNLS

noncomputable def reflectPolynomial (p : Polynomial ℂ) : Polynomial ℂ := p.comp (C (-1) * X)

theorem coeff_reflectPolynomial (p : Polynomial ℂ) (n : ℕ) :
    (reflectPolynomial p).coeff n = p.coeff n * (-1) ^ n := by
  rw [reflectPolynomial, comp_C_mul_X_coeff]

theorem reflectPolynomial_add (p q : Polynomial ℂ) :
    reflectPolynomial (p + q) = reflectPolynomial p + reflectPolynomial q := by
  simp [reflectPolynomial]

theorem reflectPolynomial_sub (p q : Polynomial ℂ) :
    reflectPolynomial (p - q) = reflectPolynomial p - reflectPolynomial q := by
  simp [reflectPolynomial]

theorem reflectPolynomial_mul (p q : Polynomial ℂ) :
    reflectPolynomial (p * q) = reflectPolynomial p * reflectPolynomial q := by
  simp [reflectPolynomial]

theorem reflectPolynomial_reflect (p : Polynomial ℂ) :
    reflectPolynomial (reflectPolynomial p) = p := by
  ext n
  rw [coeff_reflectPolynomial, coeff_reflectPolynomial, mul_assoc, ← mul_pow]
  simp

theorem reflectPolynomial_conjugate (p : Polynomial ℂ) :
    reflectPolynomial (conjugatePolynomial p) = conjugatePolynomial (reflectPolynomial p) := by
  ext n
  simp only [coeff_reflectPolynomial, coeff_conjugatePolynomial, star_mul, star_pow]
  simp [mul_comm]

theorem sharpPolynomial_eq_reflect (p : Polynomial ℂ) :
    sharpPolynomial p = reflectPolynomial (conjugatePolynomial p) := rfl

theorem reflectedHermitian_reflect_conjugate (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (i j : Fin 2) :
    reflectPolynomial (reflectedHermitianPolynomial M s T i j) =
      conjugatePolynomial (reflectedHermitianPolynomial M s T i j) := by
  unfold reflectedHermitianPolynomial
  rw [reflectPolynomial_add, conjugatePolynomial_add, sharpPolynomial_eq_reflect,
    reflectPolynomial_reflect, ← reflectPolynomial_conjugate,
    conjugatePolynomial_conjugate]
  exact add_comm _ _

theorem reflectedHermitian_conjugate_transpose (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (hs : s.re = 0) (i j : Fin 2) :
    conjugatePolynomial (reflectedHermitianPolynomial M s T j i) =
      reflectedHermitianPolynomial M s T i j := by
  unfold reflectedHermitianPolynomial
  rw [conjugatePolynomial_add, sharpPolynomial_eq_reflect, ← reflectPolynomial_conjugate,
    conjugatePolynomial_conjugate, hermitianPolynomial_conjugate M s T hs]
  rw [sharpPolynomial_eq_reflect, hermitianPolynomial_conjugate M s T hs]

theorem boundaryDeterminantPolynomial_real (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ)
    (hs : s.re = 0) :
    conjugatePolynomial (boundaryDeterminantPolynomial M s a K) =
      boundaryDeterminantPolynomial M s a K := by
  unfold boundaryDeterminantPolynomial
  simp only [conjugatePolynomial_sub, conjugatePolynomial_mul,
    conjugatePolynomial_conjugate,
    reflectedHermitian_conjugate_transpose M s _ hs 0 0,
    reflectedHermitian_conjugate_transpose M s _ hs 1 1]
  ring

theorem boundaryDeterminantPolynomial_even (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ)
    (hs : s.re = 0) :
    reflectPolynomial (boundaryDeterminantPolynomial M s a K) =
      boundaryDeterminantPolynomial M s a K := by
  unfold boundaryDeterminantPolynomial
  simp only [reflectPolynomial_sub, reflectPolynomial_mul,
    reflectedHermitian_reflect_conjugate, reflectPolynomial_conjugate,
    reflectedHermitian_conjugate_transpose M s _ hs 0 0,
    reflectedHermitian_conjugate_transpose M s _ hs 1 1,
    conjugatePolynomial_conjugate]
  ring

theorem boundaryDeterminantPolynomial_coeff_im (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K n : ℕ)
    (hs : s.re = 0) : ((boundaryDeterminantPolynomial M s a K).coeff n).im = 0 := by
  have h := congrArg (fun p : Polynomial ℂ => (p.coeff n).im)
    (boundaryDeterminantPolynomial_real M s a K hs)
  simp only [coeff_conjugatePolynomial, Complex.star_def, Complex.conj_im] at h
  linarith

theorem boundaryDeterminantPolynomial_coeff_odd (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K n : ℕ)
    (hs : s.re = 0) (hn : Odd n) : (boundaryDeterminantPolynomial M s a K).coeff n = 0 := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff n)
    (boundaryDeterminantPolynomial_even M s a K hs)
  rw [coeff_reflectPolynomial, hn.neg_one_pow] at h
  linear_combination (-1 / 2 : ℂ) * h

end DefocusingNLS

end OAI
