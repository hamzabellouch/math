import Mathlib
import OAI.Analysis.LaughlinFock.FiniteCoupling

namespace OAI

/-! Oscillator Limit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial
open Filter Topology

 

def monomialWeight (T p : ℕ) : ℝ :=
  Real.sqrt ((p.factorial : ℝ) * (T-p).factorial)

def monomialCoefficient (T : ℕ) (P : Polynomial ℝ) (p : ℕ) : ℝ :=
  monomialWeight T p * P.coeff p

theorem monomialWeight_left (T p : ℕ) :
    monomialWeight (T+1) (p+1) = Real.sqrt (p+1 : ℕ) * monomialWeight T p := by
  unfold monomialWeight
  rw [Nat.add_sub_add_right, Nat.factorial_succ, Nat.cast_mul, mul_assoc,
    Real.sqrt_mul (Nat.cast_nonneg _)]

theorem monomialWeight_right {T p : ℕ} (hp : p ≤ T) :
    monomialWeight (T+1) p = Real.sqrt (((T+1 : ℕ) : ℝ)-p) * monomialWeight T p := by
  have hs : T+1-p = (T-p)+1 := by omega
  unfold monomialWeight
  rw [hs, Nat.factorial_succ, Nat.cast_mul]
  have ht : (((T-p+1 : ℕ) : ℝ)) = ((T+1 : ℕ) : ℝ)-p := by
    rw [Nat.cast_add, Nat.cast_sub hp, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    ring
  rw [ht, mul_left_comm, Real.sqrt_mul (sub_nonneg.mpr (by
    exact_mod_cast (by omega : p ≤ T+1)))]

 

theorem monomialCoefficient_linear (P : Polynomial ℝ) (T : ℕ)
    (hP : P.natDegree ≤ T) (u v : ℝ) (p : ℕ) :
    monomialCoefficient (T+1) ((C v * X + C u) * P) p =
      (if p = 0 then 0 else Real.sqrt (p : ℝ) * v * monomialCoefficient T P (p-1)) +
        Real.sqrt (((T+1 : ℕ) : ℝ)-p) * u * monomialCoefficient T P p := by
  cases p with
  | zero =>
    simp only [monomialCoefficient, Nat.cast_zero, sub_zero, ite_true, zero_add,
      add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul_zero, mul_zero]
    rw [monomialWeight_right (by omega : 0 ≤ T)]
    simp only [Nat.cast_zero, sub_zero]
    ring
  | succ p =>
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false,
      monomialCoefficient, add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]
    by_cases hp : p+1 ≤ T
    · have hl := monomialWeight_left T p
      have hr := monomialWeight_right hp
      calc
        _ = monomialWeight (T+1) (p+1) * (v * P.coeff p) +
            monomialWeight (T+1) (p+1) * (u * P.coeff (p+1)) := by ring
        _ = (Real.sqrt (p+1 : ℕ) * monomialWeight T p) * (v * P.coeff p) +
            (Real.sqrt (((T+1 : ℕ) : ℝ)-(p+1 : ℕ)) * monomialWeight T (p+1)) *
              (u * P.coeff (p+1)) := by
          exact congrArg₂ (· + ·) (congrArg (fun x => x * (v * P.coeff p)) hl)
            (congrArg (fun x => x * (u * P.coeff (p+1))) hr)
        _ = _ := by ring
    · have hc : P.coeff (p+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [hc, mul_zero, add_zero, monomialWeight_left]
      ring

 

def couplingPolynomial (u v : ℝ) (z k : ℕ) : Polynomial ℝ :=
  (C u * X - C v)^z * (C v * X + C u)^k

def polynomialCouplingCoefficient (u v : ℝ) (z k p : ℕ) : ℝ :=
  monomialCoefficient (z+k) (couplingPolynomial u v z k) p /
    Real.sqrt ((z.factorial : ℝ) * k.factorial)

theorem couplingPolynomial_degree (u v : ℝ) (z k : ℕ) :
    (couplingPolynomial u v z k).natDegree ≤ z+k := by
  have h1 : (C u * X - C v).natDegree ≤ 1 := by
    change _ ≤ max 1 1
    apply natDegree_sub_le_of_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  have h2 : (C v * X + C u).natDegree ≤ 1 := by
    change _ ≤ max 1 1
    apply natDegree_add_le_of_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  exact natDegree_mul_le.trans (add_le_add
    (natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left z h1))
    (natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k h2)))

theorem polynomialCouplingCoefficient_zero (u v : ℝ) (z k p : ℕ) (hp : z+k < p) :
    polynomialCouplingCoefficient u v z k p = 0 := by
  have h := coeff_eq_zero_of_natDegree_lt ((couplingPolynomial_degree u v z k).trans_lt hp)
  simp only [polynomialCouplingCoefficient, monomialCoefficient, h, mul_zero, zero_div]

theorem couplingPolynomial_succ (u v : ℝ) (z k : ℕ) :
    couplingPolynomial u v z (k+1) =
      (C v * X + C u) * couplingPolynomial u v z k := by
  unfold couplingPolynomial
  rw [pow_succ]
  ring

theorem coefficient_scale_succ (z k : ℕ) :
    Real.sqrt ((z.factorial : ℝ) * (k+1).factorial) =
      Real.sqrt (k+1 : ℕ) * Real.sqrt ((z.factorial : ℝ) * k.factorial) := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_left_comm, Real.sqrt_mul (Nat.cast_nonneg _)]

 
theorem polynomialCouplingCoefficient_succ (u v : ℝ) (z k p : ℕ) :
    polynomialCouplingCoefficient u v z (k+1) p =
      ((if p = 0 then 0 else Real.sqrt (p : ℝ) * v * polynomialCouplingCoefficient u v z k (p-1)) +
        Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * u * polynomialCouplingCoefficient u v z k p) /
        Real.sqrt (k+1 : ℕ) := by
  unfold polynomialCouplingCoefficient
  rw [couplingPolynomial_succ, show z+(k+1) = z+k+1 by omega,
    monomialCoefficient_linear _ _ (couplingPolynomial_degree u v z k),
    coefficient_scale_succ]
  split_ifs <;> ring

theorem coeff_linear_pow (u v : ℝ) (z p : ℕ) :
    ((C u * X - C v)^z).coeff p = (-v)^(z-p) * (z.choose p : ℝ) * u^p := by
  have h : (C u * X - C v)^z = ((X + C (-v))^z).comp (C u * X) := by simp [sub_eq_add_neg]
  rw [h, comp_C_mul_X_coeff, coeff_X_add_C_pow]

theorem sqrt_nat_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a^n) = (Real.sqrt a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih, pow_succ]

 

theorem binomial_monomialWeight {z p : ℕ} (hp : p ≤ z) :
    (z.choose p : ℝ) * monomialWeight z p / Real.sqrt (z.factorial : ℝ) =
      Real.sqrt (z.choose p : ℝ) := by
  have hfac : (z.choose p : ℝ) * (p.factorial : ℝ) * (z-p).factorial =
      (z.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hfac0 : (z.factorial : ℝ) ≠ 0 := by positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ ((p.factorial : ℝ) * (z-p).factorial))
  have hsq : ((z.choose p : ℝ) * monomialWeight z p / Real.sqrt (z.factorial : ℝ))^2 =
      (Real.sqrt (z.choose p : ℝ))^2 := by
    rw [div_pow, mul_pow, monomialWeight, hs, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    apply (div_eq_iff hfac0).mpr
    nlinarith only [hfac]
  have hleft : 0 ≤ ((z.choose p : ℝ) * monomialWeight z p / Real.sqrt (z.factorial : ℝ)) := by
    unfold monomialWeight
    positivity
  nlinarith [Real.sqrt_nonneg (z.choose p : ℝ)]

 
theorem polynomialCouplingCoefficient_top (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (z p : ℕ) :
    polynomialCouplingCoefficient (Real.sqrt r) (Real.sqrt (1-r)) z 0 p =
      oscillatorCoefficient r z 0 p := by
  by_cases hp : p ≤ z
  · simp only [polynomialCouplingCoefficient, couplingPolynomial, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, monomialCoefficient, Nat.add_zero, coeff_linear_pow,
      oscillatorCoefficient]
    rw [neg_pow, Real.sqrt_mul (by positivity : 0 ≤ (z.choose p : ℝ) * (1-r)^(z-p)),
      Real.sqrt_mul (Nat.cast_nonneg _), sqrt_nat_pow (by linarith : 0 ≤ 1-r), sqrt_nat_pow hr]
    calc
      _ = (-1 : ℝ)^(z-p) * ((z.choose p : ℝ) * monomialWeight z p /
          Real.sqrt (z.factorial : ℝ)) * (Real.sqrt (1-r))^(z-p) * (Real.sqrt r)^p := by ring
      _ = _ := by rw [binomial_monomialWeight hp]; ring
  · rw [polynomialCouplingCoefficient_zero _ _ _ _ _ (by omega),
      oscillatorCoefficient_zero _ _ _ _ (by omega)]

 

theorem oscillatorCoefficient_eq_polynomial (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (z k p : ℕ) :
    oscillatorCoefficient r z k p =
      polynomialCouplingCoefficient (Real.sqrt r) (Real.sqrt (1-r)) z k p := by
  induction k generalizing p with
  | zero => exact (polynomialCouplingCoefficient_top r hr hr1 z p).symm
  | succ k ih =>
    rw [oscillatorCoefficient, polynomialCouplingCoefficient_succ, ih p, ih (p-1)]
    rw [Real.sqrt_mul (Nat.cast_nonneg p)]

 

theorem coupledCoefficient_polynomial_limit (n m : ℕ → ℕ) (u : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 (u^2)))
    (z k p : ℕ) :
    Tendsto (fun Q => coupledCoefficient (n Q) (m Q) z k p) atTop
      (𝓝 (polynomialCouplingCoefficient u (Real.sqrt (1-u^2)) z k p)) := by
  have h := coupledCoefficient_tendsto n m (u^2) hn hm hr z k p
  rw [oscillatorCoefficient_eq_polynomial _ (sq_nonneg _) (by nlinarith) z k p,
    Real.sqrt_sq hu0.le] at h
  exact h

end LaughlinFock
end

end OAI
