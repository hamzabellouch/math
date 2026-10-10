import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerrePolynomial

namespace OAI

/-! # Algebraic Laguerre orthogonality

The factorial moment functional realizes integration against `exp (-t)` on
the positive ray. Integration by parts becomes a finite polynomial identity.
-/

namespace DefocusingNLS

open Polynomial

noncomputable def laguerreMoment : ℂ[X] →ₗ[ℂ] ℂ :=
  Polynomial.lsum fun n => (n.factorial : ℂ) • LinearMap.id

@[simp] theorem laguerreMoment_monomial (n : ℕ) (a : ℂ) :
    laguerreMoment (monomial n a) = (n.factorial : ℂ) * a := by
  simp [laguerreMoment, Polynomial.lsum]

@[simp] theorem laguerreMoment_C (a : ℂ) : laguerreMoment (C a) = a := by
  simpa using laguerreMoment_monomial 0 a

@[simp] theorem laguerreMoment_C_mul (a : ℂ) (p : ℂ[X]) :
    laguerreMoment (C a * p) = a * laguerreMoment p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- The boundary term in integration by parts at zero. -/
theorem laguerreMoment_derivative_sub (p : ℂ[X]) :
    laguerreMoment (p.derivative - p) = -p.coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, map_sub, Polynomial.coeff_add] at hp hq ⊢
      linear_combination hp + hq
  | monomial n a =>
      cases n with
      | zero => simp
      | succ n =>
          simp [Nat.factorial_succ]
          ring

noncomputable def laguerreOperator (p : ℂ[X]) : ℂ[X] :=
  X * p.derivative.derivative + (1 - X) * p.derivative

/-- The Laguerre operator is symmetric for the factorial moment functional. -/
theorem laguerreMoment_green (p q : ℂ[X]) :
    laguerreMoment (laguerreOperator p * q) =
      -laguerreMoment (X * p.derivative * q.derivative) := by
  have h := laguerreMoment_derivative_sub (X * p.derivative * q)
  have he : (X * p.derivative * q).derivative - X * p.derivative * q =
      laguerreOperator p * q + X * p.derivative * q.derivative := by
    simp only [laguerreOperator, Polynomial.derivative_mul, Polynomial.derivative_X]
    ring
  rw [he, map_add] at h
  simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, neg_zero] at h
  linear_combination h

theorem laguerreOperator_laguerrePolynomial (n : ℕ) :
    laguerreOperator (laguerrePolynomial n) = -C (n : ℂ) * laguerrePolynomial n := by
  have h := laguerrePolynomial_differential_equation n
  dsimp [laguerreOperator]
  linear_combination h

theorem laguerreMoment_orthogonal (n m : ℕ) (hnm : n ≠ m) :
    laguerreMoment (laguerrePolynomial n * laguerrePolynomial m) = 0 := by
  have hn := laguerreMoment_green (laguerrePolynomial n) (laguerrePolynomial m)
  have hm := laguerreMoment_green (laguerrePolynomial m) (laguerrePolynomial n)
  rw [laguerreOperator_laguerrePolynomial] at hn hm
  simp only [neg_mul, mul_assoc, map_neg, laguerreMoment_C_mul] at hn hm
  rw [mul_comm (laguerrePolynomial m) (laguerrePolynomial n)] at hm
  have he : X * (laguerrePolynomial m).derivative * (laguerrePolynomial n).derivative =
      X * (laguerrePolynomial n).derivative * (laguerrePolynomial m).derivative := by ring
  simp only [mul_assoc] at he
  rw [he] at hm
  have hz : ((n : ℂ) - m) *
      laguerreMoment (laguerrePolynomial n * laguerrePolynomial m) = 0 := by
    linear_combination hm - hn
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hnm))

theorem laguerreMoment_derivative_self (n : ℕ) :
    laguerreMoment ((laguerrePolynomial n).derivative * laguerrePolynomial n) = 0 := by
  rw [laguerrePolynomial_derivative, neg_mul, map_neg, Finset.sum_mul, map_sum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro j hj
  exact laguerreMoment_orthogonal j n (Nat.ne_of_lt (Finset.mem_range.mp hj))

/-- This normalization gives squared norm one for every degree. -/
theorem laguerreMoment_self (n : ℕ) :
    laguerreMoment (laguerrePolynomial n * laguerrePolynomial n) = 1 := by
  have h := laguerreMoment_derivative_sub (laguerrePolynomial n * laguerrePolynomial n)
  rw [Polynomial.derivative_mul, map_sub, map_add,
    laguerreMoment_derivative_self, mul_comm (laguerrePolynomial n),
    laguerreMoment_derivative_self] at h
  simp only [Polynomial.mul_coeff_zero, coeff_laguerrePolynomial,
    laguerreCoefficient_zero, mul_one] at h
  linear_combination -h

theorem laguerreMoment_orthonormal (n m : ℕ) :
    laguerreMoment (laguerrePolynomial n * laguerrePolynomial m) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst m
    exact laguerreMoment_self n
  · exact laguerreMoment_orthogonal n m h

end DefocusingNLS

end OAI
