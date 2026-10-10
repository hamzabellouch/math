import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace OAI

universe uR

/-!
# Paired coefficients in a dyadic cyclotomic remainder

Reducing a polynomial of length `2 * m` modulo `X ^ m + 1` subtracts
the upper block of coefficients from the lower block. The construction
and the coefficient formulas work over every commutative ring.
-/

noncomputable section

namespace CirculantHadamard.DyadicRemainder

open Polynomial Finset

variable {R : Type uR} [CommRing R]

/-- The polynomial with the first `n` entries of a coefficient function. -/
def coefficientPolynomial (n : ℕ) (c : ℕ → R) : R[X] :=
  ∑ i ∈ range n, monomial i (c i)

/-- The difference between coefficient blocks at distance `m`. -/
def remainder (m : ℕ) (c : ℕ → R) : R[X] :=
  coefficientPolynomial m (fun i => c i - c (i + m))

@[simp]
theorem coefficientPolynomial_coeff (n : ℕ) (c : ℕ → R) (j : ℕ) :
    (coefficientPolynomial n c).coeff j = if j < n then c j else 0 := by
  classical
  simp [coefficientPolynomial, coeff_monomial]

theorem degree_coefficientPolynomial_lt (n : ℕ) (c : ℕ → R) :
    (coefficientPolynomial n c).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  simp only [coefficientPolynomial_coeff, ite_eq_right (not_lt.mpr hj)]

theorem natDegree_coefficientPolynomial_lt {n : ℕ} (hn : 0 < n) (c : ℕ → R) :
    (coefficientPolynomial n c).natDegree < n := by
  by_cases hzero : coefficientPolynomial n c = 0
  · simpa only [hzero, natDegree_zero] using hn
  · exact (natDegree_lt_iff_degree_lt hzero).mpr (degree_coefficientPolynomial_lt n c)

@[simp]
theorem remainder_coeff (m : ℕ) (c : ℕ → R) (j : ℕ) (hj : j < m) :
    (remainder m c).coeff j = c j - c (j + m) := by
  simp only [remainder, coefficientPolynomial_coeff, ite_eq_left hj]

theorem remainder_coeff_eq_zero (m : ℕ) (c : ℕ → R) (j : ℕ) (hj : m ≤ j) :
    (remainder m c).coeff j = 0 := by
  simp only [remainder, coefficientPolynomial_coeff, ite_eq_right (not_lt.mpr hj)]

theorem degree_remainder_lt (m : ℕ) (c : ℕ → R) :
    (remainder m c).degree < (m : WithBot ℕ) :=
  degree_coefficientPolynomial_lt m _

theorem natDegree_remainder_lt {m : ℕ} (hm : 0 < m) (c : ℕ → R) :
    (remainder m c).natDegree < m :=
  natDegree_coefficientPolynomial_lt hm _

theorem remainder_eq_sub (m : ℕ) (c : ℕ → R) :
    remainder m c = coefficientPolynomial m c -
      coefficientPolynomial m (fun i => c (i + m)) := by
  simp only [remainder, coefficientPolynomial, monomial_sub, sum_sub_distrib]

/-- Split the coefficient polynomial into its lower and upper blocks. -/
theorem coefficientPolynomial_two_mul (m : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
      X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
  classical
  calc
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
        ∑ i ∈ range m, monomial (m + i) (c (m + i)) := by
      rw [two_mul]
      exact sum_range_add (fun i => monomial i (c i)) m m
    _ = coefficientPolynomial m c +
        X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
      congr 1
      simp only [coefficientPolynomial, mul_sum, X_pow_mul_monomial]
      apply sum_congr rfl
      intro i _
      rw [Nat.add_comm m i]

/-- The explicit quotient/remainder equation before applying monic division. -/
theorem remainder_add_mul (m : ℕ) (c : ℕ → R) :
    remainder m c + (X ^ m + 1) *
      coefficientPolynomial m (fun i => c (i + m)) = coefficientPolynomial (2 * m) c := by
  rw [remainder_eq_sub, add_mul, one_mul,
    add_comm (X ^ m * coefficientPolynomial m (fun i => c (i + m)))
      (coefficientPolynomial m (fun i => c (i + m))),
    ← add_assoc, sub_add_cancel]
  exact (coefficientPolynomial_two_mul m c).symm

/-- The canonical monic remainder is exactly the paired coefficient difference. -/
theorem coefficientPolynomial_modByMonic {m : ℕ} (hm : 0 < m) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c %ₘ (X ^ m + 1) = remainder m c := by
  nontriviality R
  have hmonic : (X ^ m + (1 : R[X])).Monic := by
    simpa only [C_1] using (monic_X_pow_add_C (1 : R) hm.ne')
  apply (div_modByMonic_unique
    (coefficientPolynomial m (fun i => c (i + m))) (remainder m c) hmonic ?_).2
  refine ⟨remainder_add_mul m c, ?_⟩
  have hdegree : (X ^ m + (1 : R[X])).degree = (m : WithBot ℕ) := by
    simpa only [C_1] using (degree_X_pow_add_C hm (1 : R))
  rw [hdegree]
  exact degree_remainder_lt m c

/-- Coefficients below the half-length in the canonical monic remainder. -/
theorem coefficientPolynomial_modByMonic_coeff {m : ℕ} (hm : 0 < m)
    (c : ℕ → R) (j : ℕ) (hj : j < m) :
    (coefficientPolynomial (2 * m) c %ₘ (X ^ m + 1)).coeff j = c j - c (j + m) := by
  rw [coefficientPolynomial_modByMonic hm, remainder_coeff m c j hj]

/-- The dyadic cyclotomic polynomial has the expected two terms. -/
theorem cyclotomic_two_pow_succ (R : Type uR) [CommRing R] (k : ℕ) :
    cyclotomic (2 ^ (k + 1)) R = (X : R[X]) ^ (2 ^ k) + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two, geom_sum_two]

/-- The remainder statement specialized to the dyadic cyclotomic polynomial. -/
theorem coefficientPolynomial_modByMonic_cyclotomic (k : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 ^ (k + 1)) c %ₘ cyclotomic (2 ^ (k + 1)) R =
      remainder (2 ^ k) c := by
  rw [cyclotomic_two_pow_succ, pow_succ, Nat.mul_comm (2 ^ k) 2]
  exact coefficientPolynomial_modByMonic (pow_pos (by decide : 0 < (2 : ℕ)) k) c

end CirculantHadamard.DyadicRemainder

end

end OAI
