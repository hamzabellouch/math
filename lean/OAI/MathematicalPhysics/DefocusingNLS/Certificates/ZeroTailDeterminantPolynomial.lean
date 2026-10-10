import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ZeroTailConjugation

namespace OAI

/-! # Exact polynomial identity for the zero-tail determinant -/

open Polynomial Matrix

namespace DefocusingNLS.SeparatorArithmetic

attribute [local irreducible] backwardCoefficients toPolynomial matchingHomotopyColumn

theorem map_gaussian_conjugate (p : Polynomial GaussianInt) :
    (p.map (starRingEnd GaussianInt)).map GaussianInt.toComplex =
      (p.map GaussianInt.toComplex).map (starRingEnd ℂ) := by
  ext n
  simp only [coeff_map, starRingEnd_apply]
  exact GaussianInt.toComplex_star (p.coeff n)

/-- The central certificate polynomial is exactly the entire zero-tail matching
determinant, with its documented spectral translation and integer scaling. -/
theorem windingPolynomial_eval_zeroTailDeterminant (ell : ℕ) (z : ℂ) :
    (2 * Complex.I) * ((windingPolynomial ell).map (Int.castRingHom ℂ)).eval z =
      (100000000 : ℂ) ^ 16 * spectralHomotopyDeterminant ell
        (33477607 / 100000000) (270506819 / 100000000) 0 (z - 1 / 32) := by
  let X := (toPolynomial (backwardCoefficients ell).1).map GaussianInt.toComplex
  let Y := (toPolynomial (backwardCoefficients ell).2).map GaussianInt.toComplex
  have hm : (toPolynomial (backwardCoefficients ell).1 *
      (toPolynomial (backwardCoefficients ell).2).map (starRingEnd GaussianInt)).map
        GaussianInt.toComplex = X * Y.map (starRingEnd ℂ) := by
    rw [Polynomial.map_mul, map_gaussian_conjugate]
  have h := congrArg (fun p : Polynomial ℂ => p.eval z)
    (windingPolynomial_complex_identity ell)
  rw [hm] at h
  simp only [eval_mul, eval_C, eval_sub, evaluate_conjugate_polynomial,
    star_mul, star_star] at h
  have hp0 : X.eval z = (100000000 : ℂ) ^ 8 *
      matchingHomotopyColumn (ell + 5) 8 zeroTailS 0 (zeroTailQ ell z) 0 := by
    simpa only [X, evaluatePair, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul] using
      congrFun (evaluatePair_backwardCoefficients ell z) 0
  have hp1 : Y.eval z = (100000000 : ℂ) ^ 8 *
      matchingHomotopyColumn (ell + 5) 8 zeroTailS 0 (zeroTailQ ell z) 1 := by
    simpa only [Y, evaluatePair, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul] using
      congrFun (evaluatePair_backwardCoefficients ell z) 1
  have hm0 : star (X.eval (star z)) = (100000000 : ℂ) ^ 8 *
      matchingHomotopyColumn (ell + 5) 8 (-zeroTailS) 0
        (spectralQ ell (-1) (33477607 / 100000000) (z - 1 / 32)) 0 := by
    simpa only [X, evaluatePair, Matrix.cons_val_zero] using evaluatePair_conjugate ell z 0
  have hm1 : star (Y.eval (star z)) = (100000000 : ℂ) ^ 8 *
      matchingHomotopyColumn (ell + 5) 8 (-zeroTailS) 0
        (spectralQ ell (-1) (33477607 / 100000000) (z - 1 / 32)) 1 := by
    simpa only [Y, evaluatePair, Matrix.cons_val_one, Matrix.cons_val_zero] using evaluatePair_conjugate ell z 1
  rw [hp0, hp1, hm0, hm1] at h
  rw [h]
  simp only [spectralHomotopyDeterminant, matchingColumnDeterminant, zeroTailQ, zeroTailS,
    Complex.ofReal_div, Complex.ofReal_ofNat, neg_mul]
  ring

end DefocusingNLS.SeparatorArithmetic

end OAI
