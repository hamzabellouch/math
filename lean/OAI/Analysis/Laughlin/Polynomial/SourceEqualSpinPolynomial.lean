import Mathlib.Algebra.Polynomial.Eval.Coeff
import OAI.Analysis.Laughlin.Polynomial.OscillatorPolynomial
import OAI.Analysis.Laughlin.Polynomial.SourceIntegerPolynomial

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem equalSpin_polynomial (u : ℝ) (z n : ℕ) :
    couplingPolynomial u u z n = C (u^(z+n)) *
      (Certificate.integerCouplingPolynomial z n).map (Int.castRingHom ℝ) := by
  simp only [couplingPolynomial,Certificate.integerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,pow_add,C_mul,C_pow]
  rw [show C u * X-C u = C u*(X-1) by ring,
    show C u * X+C u = C u*(X+1) by ring,mul_pow,mul_pow]
  ring

theorem equalSpin_polynomialCoefficient (u : ℝ) (z n p : ℕ) (hp : p ≤ z+n) :
    couplingPolynomialCoefficient u u z n p =
      u^(z+n) * (Certificate.U 1 z (z+n) p : ℝ) *
        sqrtFactorial p * sqrtFactorial (z+n-p) / (sqrtFactorial z * sqrtFactorial n) := by
  unfold couplingPolynomialCoefficient
  rw [equalSpin_polynomial,coeff_C_mul,coeff_map,Certificate.integerCouplingPolynomial_coeff z n p hp]
  simp only [Int.coe_castRingHom,monomialNormFactor]
  ring

end Laughlin.Spin

end OAI
