import OAI.Analysis.Laughlin.Polynomial.OscillatorPolynomial
import OAI.Analysis.Laughlin.ThreeBody.IntegerPolynomial

namespace OAI

namespace Laughlin.Spin
open Polynomial

theorem threeBody_scaled_polynomial (u w : ℝ) (hw : w^2=2) (hw0 : w ≠ 0) (z n : ℕ) :
    couplingPolynomial u (w*u) z n = C (u^(z+n)*w^z) *
      ((Certificate.weightedIntegerCouplingPolynomial 2 z n).map (Int.castRingHom ℝ)).comp (C w⁻¹*X) := by
  have h2 : (2 : ℝ)*w⁻¹=w := by
    field_simp
    nlinarith only [hw]
  simp only [Certificate.weightedIntegerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,Polynomial.map_C,
    Int.coe_castRingHom,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,Polynomial.add_comp,
    Polynomial.X_comp,Polynomial.C_comp,Polynomial.one_comp]
  norm_num only [Nat.cast_ofNat,Int.cast_natCast]
  rw [show C (2 : ℝ)*(C w⁻¹*X) = C w*X by rw [← mul_assoc,← C_mul,h2]]
  have he : C u*X-C (w*u) = C (u*w)*(C w⁻¹*X-1) := by
    have hc : u*w*w⁻¹=u := by field_simp
    simp only [mul_sub,← mul_assoc,← C_mul,mul_one,hc]
    rw [mul_comm w u]
  have hf : C (w*u)*X+C u = C u*(C w*X+1) := by
    simp only [mul_add,← mul_assoc,← C_mul,mul_one]
    rw [mul_comm w u]
  unfold couplingPolynomial
  rw [he,hf,mul_pow,mul_pow,← C_pow,← C_pow]
  simp only [pow_add,mul_pow,C_mul]
  ring

theorem threeBody_polynomialCoefficient_factorial (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p =
      (Certificate.U 2 z T p : ℝ) * (Real.sqrt (1/3))^T *
      (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z)) := by
  have hs : Real.sqrt (2/3) = Real.sqrt 2 * Real.sqrt (1/3) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hT : z+(T-z)=T := by omega
  unfold couplingPolynomialCoefficient
  rw [hs,threeBody_scaled_polynomial _ _ (Real.sq_sqrt (by norm_num)) (by positivity),
    coeff_C_mul,comp_C_mul_X_coeff,coeff_map,
    Certificate.weightedIntegerCouplingPolynomial_coeff 2 z (T-z) p (by omega)]
  simp only [Int.coe_castRingHom,hT,monomialNormFactor,inv_pow]
  ring

end Laughlin.Spin

end OAI
