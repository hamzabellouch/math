import Mathlib
import OAI.Analysis.LaughlinFock.OscillatorLimit

namespace OAI

/-! Rational Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Polynomial

 
def rationalCoupling (c : ℚ) (z k p : ℕ) : ℚ :=
  (((X-1)^z * (C c*X+1)^k) : Polynomial ℚ).coeff p

 

def rationalCouplingWeight (c : ℚ) (z k p : ℕ) : ℚ :=
  c^z * ((p.factorial : ℚ) * (z+k-p).factorial) /
    ((1+c)^(z+k) * c^p * (z.factorial : ℚ) * k.factorial)

theorem couplingPolynomial_rescale (c u v : ℝ) (_hu : u ≠ 0) (hv : v ≠ 0)
    (hc : c*u^2 = v^2) (z k : ℕ) :
    couplingPolynomial u v z k =
      C (v^z*u^k) * (((X-1)^z*(C c*X+1)^k).comp (C (u/v)*X)) := by
  have h1 : (C v : Polynomial ℝ) * (C (u/v)*X-1) = C u*X-C v := by
    simp only [mul_sub, mul_one, ← mul_assoc, ← C_mul]
    congr 2
    field_simp
  have h2 : (C u : Polynomial ℝ) * (C c*(C (u/v)*X)+1) = C v*X+C u := by
    simp only [mul_add, mul_one, ← mul_assoc, ← C_mul]
    congr 2
    congr 1
    field_simp
    nlinarith only [hc]
  simp only [couplingPolynomial, mul_comp, pow_comp, sub_comp, add_comp, X_comp,
    one_comp, C_comp]
  rw [show C (v^z*u^k) = (C v)^z*(C u)^k by simp, mul_mul_mul_comm,
    ← mul_pow, ← mul_pow, h1, h2]

theorem polynomialCouplingCoefficient_rescale (c u v : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hc : c*u^2=v^2) (z k p : ℕ) :
    polynomialCouplingCoefficient u v z k p =
      (((X-1)^z*(C c*X+1)^k : Polynomial ℝ).coeff p) *
      (monomialWeight (z+k) p / Real.sqrt ((z.factorial : ℝ)*k.factorial) *
        (v^z*u^k*(u/v)^p)) := by
  simp only [polynomialCouplingCoefficient, monomialCoefficient,
    couplingPolynomial_rescale c u v hu hv hc, coeff_C_mul, comp_C_mul_X_coeff]
  ring

theorem rationalCoupling_real (c : ℚ) (z k p : ℕ) :
    (((X-1)^z * (C (c : ℝ)*X+1)^k) : Polynomial ℝ).coeff p =
      (rationalCoupling c z k p : ℝ) := by
  have h : (((X-1)^z * (C c*X+1)^k) : Polynomial ℚ).map (algebraMap ℚ ℝ) =
      ((X-1)^z*(C (c:ℝ)*X+1)^k) := by simp
  rw [← h, Polynomial.coeff_map]
  rfl

 

theorem polynomialCouplingCoefficient_rational (c : ℚ) (hc : 0 < c)
    (z k p : ℕ) :
    polynomialCouplingCoefficient (Real.sqrt (1/(1+(c:ℝ))))
      (Real.sqrt ((c:ℝ)/(1+(c:ℝ)))) z k p =
      (rationalCoupling c z k p : ℝ) * Real.sqrt (rationalCouplingWeight c z k p : ℝ) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hC : (0:ℝ) < 1+(c:ℝ) := by linarith
  let u := Real.sqrt (1/(1+(c:ℝ)))
  let v := Real.sqrt ((c:ℝ)/(1+(c:ℝ)))
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos zero_lt_one hC)
  have hv : 0 < v := Real.sqrt_pos.mpr (div_pos hcR hC)
  have hu2 : u^2 = 1/(1+(c:ℝ)) := Real.sq_sqrt (by positivity)
  have hv2 : v^2 = (c:ℝ)/(1+(c:ℝ)) := Real.sq_sqrt (by positivity)
  have huv2 : (u/v)^2 = 1/(c:ℝ) := by
    rw [div_pow, hu2, hv2]
    field_simp
  rw [polynomialCouplingCoefficient_rescale (c:ℝ) u v hu.ne' hv.ne'
    (by rw [hu2, hv2]; ring), rationalCoupling_real]
  congr 1
  let f : ℝ := monomialWeight (z+k) p / Real.sqrt ((z.factorial : ℝ)*k.factorial) *
      (v^z*u^k*(u/v)^p)
  have hf : 0 ≤ f := by dsimp [f, monomialWeight]; positivity
  have hs : f^2 = (rationalCouplingWeight c z k p : ℝ) := by
    dsimp [f, monomialWeight, rationalCouplingWeight]
    push_cast
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      mul_pow, mul_pow, ← pow_mul, mul_comm z 2, pow_mul, hv2,
      ← pow_mul, mul_comm k 2, pow_mul, hu2,
      ← pow_mul, mul_comm p 2, pow_mul, huv2]
    simp only [div_pow, one_pow, pow_add]
    field_simp
  rw [← hs, Real.sqrt_sq hf]

end LaughlinFock
end

end OAI
