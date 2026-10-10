import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ZeroTailRecurrenceLink
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CenteredPolynomial

namespace OAI

/-! # Conjugation of the two zero-tail matching channels -/

open Polynomial Matrix

namespace DefocusingNLS.SeparatorArithmetic

attribute [local irreducible] backwardProduct backwardCoefficients toPolynomial windingPolynomial matchingHomotopyColumn

theorem backwardProduct_conjugate (M : ℝ) (s q : ℂ) (N : ℕ) (i j : Fin 2) :
    star (backwardProduct (M : ℂ) s q N i j) =
      backwardProduct (M : ℂ) (star s) (star q) N i j := by
  induction N generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [backwardProduct]
  | succ N ih =>
    simp only [backwardProduct, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul, ih]
    have hs (a b : Fin 2) : star (backwardMatrix (M : ℂ) s (q + N) a b) =
        backwardMatrix (M : ℂ) (star s) (star q + N) a b := by
      fin_cases a <;> fin_cases b <;> simp [backwardMatrix]
    rw [hs, hs]
    ring

theorem zeroTailQ_conjugate (ell : ℕ) (z : ℂ) :
    star (zeroTailQ ell (star z)) =
      spectralQ ell (-1) (33477607 / 100000000) (z - 1 / 32) := by
  apply Complex.ext <;>
    simp [zeroTailQ, spectralQ, Complex.mul_re, Complex.mul_im]

theorem zeroTailS_conjugate : star zeroTailS = -zeroTailS := by
  simp [zeroTailS]

theorem evaluate_conjugate_polynomial (p : Polynomial ℂ) (z : ℂ) :
    (p.map (starRingEnd ℂ)).eval z = star (p.eval (star z)) := by
  simpa only [starRingEnd_apply, star_star] using
    (Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) (star z))

theorem evaluatePair_conjugate (ell : ℕ) (z : ℂ) (i : Fin 2) :
    star (evaluatePair (backwardCoefficients ell) (star z) i) =
      (100000000 : ℂ) ^ 8 *
        matchingHomotopyColumn (ell + 5) 8 (-zeroTailS) 0
          (spectralQ ell (-1) (33477607 / 100000000) (z - 1 / 32)) i := by
  rw [evaluatePair_backwardCoefficients, Pi.smul_apply, smul_eq_mul, star_mul]
  simp only [star_pow, star_ofNat]
  rw [matchingHomotopyColumn_zero, matchingHomotopyColumn_zero]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_add]
  have h := backwardProduct_conjugate (ell + 5 : ℕ) zeroTailS (zeroTailQ ell (star z)) 8 i 1
  simp only [Nat.cast_add, Nat.cast_ofNat, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_ofNat] at h ⊢
  rw [h, zeroTailQ_conjugate, zeroTailS_conjugate]
  ring

/-- The imaginary-part coefficients encode the full determinant polynomial,
not merely its values on the real axis. -/
theorem windingPolynomial_complex_identity (ell : ℕ) :
    C (2 * Complex.I) * (windingPolynomial ell).map (Int.castRingHom ℂ) =
      (toPolynomial (backwardCoefficients ell).1 *
        (toPolynomial (backwardCoefficients ell).2).map (starRingEnd GaussianInt)).map
          GaussianInt.toComplex -
      ((toPolynomial (backwardCoefficients ell).1 *
        (toPolynomial (backwardCoefficients ell).2).map (starRingEnd GaussianInt)).map
          GaussianInt.toComplex).map (starRingEnd ℂ) := by
  ext n
  simp only [coeff_C_mul, coeff_map, coeff_sub, coeff_windingPolynomial, windingCoefficient_eq,
    starRingEnd_apply]
  generalize (toPolynomial (backwardCoefficients ell).1 *
    (toPolynomial (backwardCoefficients ell).2).map (starRingEnd GaussianInt)).coeff n = a
  change (2 * Complex.I) * (a.im : ℂ) = (a : ℂ) - star (a : ℂ)
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.star_def, Complex.conj_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_im,
      Complex.star_def, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    (norm_num; ring)

end DefocusingNLS.SeparatorArithmetic

end OAI
