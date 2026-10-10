import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-! # The Laguerre polynomials used in the slow-solution projection

The normalization is `Lₙ(0) = 1`, with weight `exp (-t)` on the positive ray.
The differential and derivative identities hold as polynomial identities.
-/

namespace DefocusingNLS

open Polynomial

noncomputable def laguerreCoefficient (n k : ℕ) : ℂ :=
  (-1) ^ k * (n.choose k : ℂ) / (k.factorial : ℂ)

noncomputable def laguerrePolynomial (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), monomial k (laguerreCoefficient n k)

theorem laguerreCoefficient_eq_zero (n k : ℕ) (h : n < k) :
    laguerreCoefficient n k = 0 := by
  simp [laguerreCoefficient, Nat.choose_eq_zero_of_lt h]

@[simp] theorem coeff_laguerrePolynomial (n k : ℕ) :
    (laguerrePolynomial n).coeff k = laguerreCoefficient n k := by
  by_cases h : k < n + 1
  · simp [laguerrePolynomial, Polynomial.coeff_monomial,
      Finset.mem_range, h]
  · have hnk : n < k := by omega
    simp [laguerrePolynomial, Polynomial.coeff_monomial,
      Finset.mem_range, h, laguerreCoefficient_eq_zero n k hnk]

@[simp] theorem laguerreCoefficient_zero (n : ℕ) : laguerreCoefficient n 0 = 1 := by
  simp [laguerreCoefficient]

@[simp] theorem laguerrePolynomial_eval_zero (n : ℕ) :
    (laguerrePolynomial n).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_laguerrePolynomial, laguerreCoefficient_zero]

@[simp] theorem laguerrePolynomial_zero : laguerrePolynomial 0 = 1 := by
  ext k
  cases k <;> simp [laguerreCoefficient, Polynomial.coeff_one]

theorem laguerreCoefficient_recurrence (n k : ℕ) :
    ((k : ℂ) + 1) ^ 2 * laguerreCoefficient n (k + 1) +
      ((n : ℂ) - k) * laguerreCoefficient n k = 0 := by
  by_cases hkn : k ≤ n
  · have hc : (n.choose (k + 1) : ℂ) * ((k : ℂ) + 1) =
        (n.choose k : ℂ) * ((n : ℂ) - k) := by
      exact_mod_cast Nat.choose_succ_right_eq n k
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [laguerreCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ]
    field_simp
    linear_combination -((-1 : ℂ) ^ k) * hc
  · have hnk : n < k := by omega
    rw [laguerreCoefficient_eq_zero n k hnk,
      laguerreCoefficient_eq_zero n (k + 1) (by omega)]
    ring

/-- `t Lₙ'' + (1-t)Lₙ' + n Lₙ = 0`, as a polynomial identity. -/
theorem laguerrePolynomial_differential_equation (n : ℕ) :
    X * (laguerrePolynomial n).derivative.derivative +
      (1 - X) * (laguerrePolynomial n).derivative +
      C (n : ℂ) * laguerrePolynomial n = 0 := by
  ext k
  cases k with
  | zero =>
      simpa [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_derivative,
        sub_mul, Polynomial.coeff_C_mul] using laguerreCoefficient_recurrence n 0
  | succ k =>
      simp only [Polynomial.coeff_add, sub_mul, one_mul,
        Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
        Polynomial.coeff_C_mul, coeff_laguerrePolynomial, Polynomial.coeff_zero]
      have h := laguerreCoefficient_recurrence n (k + 1)
      push_cast at h ⊢
      linear_combination h

theorem laguerreCoefficient_derivative_step (n k : ℕ) :
    ((k : ℂ) + 1) * (laguerreCoefficient (n + 1) (k + 1) -
      laguerreCoefficient n (k + 1)) = -laguerreCoefficient n k := by
  have hc : ((n + 1).choose (k + 1) : ℂ) =
      (n.choose k : ℂ) + (n.choose (k + 1) : ℂ) := by
    exact_mod_cast Nat.choose_succ_succ' n k
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [laguerreCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  rw [hc]
  field_simp
  ring

theorem laguerrePolynomial_derivative_step (n : ℕ) :
    (laguerrePolynomial (n + 1)).derivative =
      (laguerrePolynomial n).derivative - laguerrePolynomial n := by
  ext k
  simp only [Polynomial.coeff_sub, Polynomial.coeff_derivative, coeff_laguerrePolynomial]
  have h := laguerreCoefficient_derivative_step n k
  linear_combination h

/-- The derivative has the finite triangular expansion used in projection. -/
theorem laguerrePolynomial_derivative (n : ℕ) :
    (laguerrePolynomial n).derivative =
      -∑ j ∈ Finset.range n, laguerrePolynomial j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [laguerrePolynomial_derivative_step, ih, Finset.sum_range_succ]
      ring

end DefocusingNLS

end OAI
