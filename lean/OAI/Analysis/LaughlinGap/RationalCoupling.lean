import Mathlib
import OAI.Analysis.LaughlinGap.ThreeComparison

namespace OAI

/-! Rational Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Polynomial
open Polynomial

noncomputable def rootFactorial (n : ℕ) : ℝ := Real.sqrt (n.factorial : ℝ)
lemma rootFactorial_pos (n : ℕ) : 0 < rootFactorial n :=
  Real.sqrt_pos.mpr (by exact_mod_cast n.factorial_pos)
lemma rootFactorial_ne_zero (n : ℕ) : rootFactorial n ≠ 0 := (rootFactorial_pos n).ne'
@[simp] lemma rootFactorial_sq (n : ℕ) : rootFactorial n ^ 2 = (n.factorial : ℝ) :=
  Real.sq_sqrt (by positivity)
@[simp] lemma rootFactorial_zero : rootFactorial 0 = 1 := by simp [rootFactorial]

lemma monomialWeight_roots (T p : ℕ) : monomialWeight T p = rootFactorial p * rootFactorial (T-p) :=
  Real.sqrt_mul (by positivity) _

noncomputable def integerCoupling (c z l : ℕ) : ℚ[X] := (X-1)^z * (C (c:ℚ)*X+1)^l

def uCoefficient (c z T p : ℕ) : ℚ :=
  if z ≤ T then ∑ h ∈ Finset.range (p+1),
    (-1:ℚ)^(z-h) * (z.choose h) * ((T-z).choose (p-h)) * (c:ℚ)^(p-h) else 0

lemma integerCoupling_coeff (c z l p : ℕ) :
    (integerCoupling c z l).coeff p =
      ∑ h ∈ Finset.range (p+1), (-1:ℚ)^(z-h) * (z.choose h) *
        (l.choose (p-h)) * (c:ℚ)^(p-h) := by
  have h₁ (h : ℕ) : ((X-1:ℚ[X])^z).coeff h = (-1:ℚ)^(z-h) * (z.choose h) := by
    simpa [sub_eq_add_neg] using coeff_X_add_C_pow (-1:ℚ) z h
  have h₂ (h : ℕ) : ((C (c:ℚ)*X+1 : ℚ[X])^l).coeff h = (l.choose h : ℚ) * (c:ℚ)^h := by
    have he : ((X+1:ℚ[X])^l).comp (C (c:ℚ)*X) = (C (c:ℚ)*X+1)^l := by simp
    rw [← he,comp_C_mul_X_coeff,coeff_X_add_one_pow]
  simp only [integerCoupling,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,h₁,h₂]
  apply Finset.sum_congr rfl
  intro h hh
  ring

lemma uCoefficient_eq_coeff {z T : ℕ} (hz : z ≤ T) (c p : ℕ) :
    uCoefficient c z T p = (integerCoupling c z (T-z)).coeff p := by
  rw [uCoefficient,ite_eq_left hz,integerCoupling_coeff]

lemma couplingPolynomial_equal (a : ℝ) (z l : ℕ) :
    couplingPolynomial a a z l =
      C (a^(z+l)/(rootFactorial z * rootFactorial l)) *
        (integerCoupling 1 z l).map (algebraMap ℚ ℝ) := by
  have ha : C a * X - C a = C a * (X-1) := by ring
  have hb : C a * X + C a = C a * (X+1) := by ring
  have he : (integerCoupling 1 z l).map (algebraMap ℚ ℝ) = (X-1)^z*(X+1)^l := by
    simp [integerCoupling]
  rw [he]
  have hc : a^(z+l)/(rootFactorial z*rootFactorial l) =
      (1/(rootFactorial z*rootFactorial l))* a^z * a^l := by rw [pow_add]; ring
  rw [hc]
  simp only [couplingPolynomial,ha,hb,mul_pow,C_mul,C_pow,rootFactorial]
  ring

lemma balancedCouplingCoefficient_rational {z T : ℕ} (hz : z ≤ T) (p : ℕ) :
    balancedCouplingCoefficient z T p = (uCoefficient 1 z T p : ℝ) *
      (rootFactorial p * rootFactorial (T-p)) /
        ((Real.sqrt 2)^T * rootFactorial z * rootFactorial (T-z)) := by
  rw [balancedCouplingCoefficient,ite_eq_left hz,couplingPolynomial_equal,
    coeff_C_mul,coeff_map,monomialWeight_roots,uCoefficient_eq_coeff hz,
    Nat.add_sub_of_le hz]
  change _ = (algebraMap ℚ ℝ _) * _ / _
  simp only [one_div,inv_pow]
  ring

lemma couplingPolynomial_scaled (a b : ℝ) (hb : b ≠ 0) (z l : ℕ) :
    couplingPolynomial a (b*a) z l =
      C (b^z*a^(z+l)/(rootFactorial z*rootFactorial l)) *
        (((X-1)^z*(C (b^2)*X+1)^l).comp (C b⁻¹*X)) := by
  have h₁ : C a * X - C (b*a) = C (b*a) * (C b⁻¹*X-1) := by
    rw [C_mul]
    have hi : (C b : ℝ[X]) * C b⁻¹ = 1 := by rw [← C_mul,mul_inv_cancel₀ hb,C_1]
    linear_combination -(C a * X) * hi
  have h₂ : C (b*a) * X + C a = C a * (C (b^2)*(C b⁻¹*X)+1) := by
    rw [pow_two,C_mul,C_mul]
    have hi : (C b : ℝ[X]) * C b⁻¹ = 1 := by rw [← C_mul,mul_inv_cancel₀ hb,C_1]
    linear_combination -(C a * C b * X) * hi
  have hc : b^z*a^(z+l)/(rootFactorial z*rootFactorial l) =
      (1/(rootFactorial z*rootFactorial l)) * (b*a)^z * a^l := by
    rw [pow_add,mul_pow]; ring
  rw [hc]
  rw [couplingPolynomial,h₁,h₂]
  simp only [mul_comp,pow_comp,sub_comp,add_comp,
    X_comp,C_comp,one_comp,mul_pow,C_mul,C_pow,rootFactorial]
  ring

lemma threeWeightCoefficientStar_rational {z T : ℕ} (hz : z ≤ T) (p : ℕ) :
    RealOccupation.threeWeightCoefficientStar z T p = (uCoefficient 2 z T p : ℝ) *
      (Real.sqrt 2)^z * rootFactorial p * rootFactorial (T-p) /
        ((Real.sqrt 3)^T * (Real.sqrt 2)^p * rootFactorial z * rootFactorial (T-z)) := by
  have hb : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [RealOccupation.threeWeightCoefficientStar,ite_eq_left hz]
  rw [show Real.sqrt 2 / Real.sqrt 3 = Real.sqrt 2 * (1/Real.sqrt 3) by ring,
    couplingPolynomial_scaled _ _ hb,coeff_C_mul,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have he : ((X-1)^z*(C (2:ℝ)*X+1)^(T-z)) =
      (integerCoupling 2 z (T-z)).map (algebraMap ℚ ℝ) := by
    simp [integerCoupling]
  rw [he,comp_C_mul_X_coeff,coeff_map,monomialWeight_roots,
    uCoefficient_eq_coeff hz,Nat.add_sub_of_le hz]
  change _ = (algebraMap ℚ ℝ _) * _ * _ * _ / _
  simp only [one_div,inv_pow]
  ring

end LaughlinGap.Spin

end

end OAI
