import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreOrthogonality
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace OAI

/-! # Integral realization of Laguerre orthogonality -/

namespace DefocusingNLS

open Polynomial MeasureTheory Set
open scoped ComplexConjugate

theorem integrableOn_exp_neg_natPow (n : ℕ) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ n) (Ioi 0) := by
  have hpos : 0 < ((n : ℂ) + 1).re := by simp; positivity
  simpa only [add_sub_cancel_right, Complex.cpow_natCast] using
    Complex.GammaIntegral_convergent hpos

theorem integral_exp_neg_natPow (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * (t : ℂ) ^ n) = n.factorial := by
  have hpos : 0 < ((n : ℂ) + 1).re := by simp; positivity
  have h := Complex.Gamma_eq_integral hpos
  rw [Complex.Gamma_nat_eq_factorial] at h
  simpa only [Complex.GammaIntegral, add_sub_cancel_right, Complex.cpow_natCast] using h.symm

theorem integrableOn_exp_neg_polynomial (p : ℂ[X]) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ) * p.eval (t : ℂ)) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert! hp.add hq using 1
      funext t
      simp only [Polynomial.eval_add, mul_add, Pi.add_apply]
  | monomial n a =>
      change Integrable _ (volume.restrict (Ioi 0))
      convert! (integrableOn_exp_neg_natPow n).const_mul a using 1
      funext t
      simp only [Polynomial.eval_monomial]
      ring

theorem integral_exp_neg_polynomial (p : ℂ[X]) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * p.eval (t : ℂ)) = laguerreMoment p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, mul_add]
      rw [integral_add (integrableOn_exp_neg_polynomial p)
        (integrableOn_exp_neg_polynomial q), hp, hq, map_add]
  | monomial n a =>
      simp only [Polynomial.eval_monomial, laguerreMoment_monomial]
      simp_rw [mul_left_comm (Real.exp (-_) : ℂ) a]
      rw [integral_const_mul, integral_exp_neg_natPow]
      ring

@[simp] theorem conj_laguerreCoefficient (n k : ℕ) :
    conj (laguerreCoefficient n k) = laguerreCoefficient n k := by
  simp [laguerreCoefficient]

@[simp] theorem conj_laguerrePolynomial_eval (n : ℕ) (t : ℝ) :
    conj ((laguerrePolynomial n).eval (t : ℂ)) =
      (laguerrePolynomial n).eval (t : ℂ) := by
  simp [laguerrePolynomial, Polynomial.eval_finsetSum, map_sum,
    Polynomial.eval_monomial]

theorem integral_laguerre_orthonormal (n m : ℕ) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) *
      conj ((laguerrePolynomial n).eval (t : ℂ)) *
      (laguerrePolynomial m).eval (t : ℂ)) = if n = m then 1 else 0 := by
  simp only [conj_laguerrePolynomial_eval]
  simp_rw [mul_assoc, ← Polynomial.eval_mul]
  rw [integral_exp_neg_polynomial, laguerreMoment_orthonormal]

end DefocusingNLS

end OAI
