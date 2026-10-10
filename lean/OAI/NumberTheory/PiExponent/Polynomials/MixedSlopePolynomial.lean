import Mathlib

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open Polynomial Finset

def mixedSlopePolynomial (d : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ range (d+1), C ((d.choose k : ℝ) * c k) * X^k

lemma mixedSlopePolynomial_eval (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (mixedSlopePolynomial d c).eval t =
      ∑ k ∈ range (d+1), (d.choose k : ℝ) * c k * t^k := by
  simp only [mixedSlopePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma mixedSlopePolynomial_eval_zero (d : ℕ) (c : ℕ → ℝ) :
    (mixedSlopePolynomial d c).eval 0 = c 0 := by
  rw [mixedSlopePolynomial_eval, Finset.sum_range_succ']
  simp

theorem mixedSlopePolynomial_derivative (d : ℕ) (c : ℕ → ℝ) :
    (mixedSlopePolynomial (d+1) c).derivative =
      C ((d+1 : ℕ) : ℝ) * mixedSlopePolynomial d (fun k => c (k+1)) := by
  unfold mixedSlopePolynomial
  rw [Polynomial.derivative_sum, Finset.sum_range_succ']
  simp only [Polynomial.derivative_C_mul_X_pow, Nat.cast_zero, mul_zero,
    C_0, zero_mul, add_zero, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h : (((d+1).choose (k+1) : ℕ) : ℝ) * ((k+1 : ℕ) : ℝ) =
      ((d+1 : ℕ) : ℝ) * (d.choose k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq d k).symm
  rw [← mul_assoc, ← C_mul]
  congr 2
  calc
    _ = (((d+1).choose (k+1) : ℝ) * ((k+1 : ℕ) : ℝ)) * c (k+1) := by ring
    _ = _ := by rw [h]; ring

lemma mixedSlopePolynomial_derivative_eval (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (mixedSlopePolynomial (d+1) c).derivative.eval t =
      (d+1 : ℕ) * (mixedSlopePolynomial d (fun k => c (k+1))).eval t := by
  rw [mixedSlopePolynomial_derivative]
  simp

theorem mixedSlopePolynomial_eval_div (d : ℕ) (c : ℕ → ℝ)
    (a b : ℝ) (hb : b ≠ 0) :
    b^d * (mixedSlopePolynomial d c).eval (a/b) =
      ∑ k ∈ range (d+1), (d.choose k : ℝ) * c k * b^(d-k) * a^k := by
  rw [mixedSlopePolynomial_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hp : b^d = b^(d-k) * b^k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [div_pow, hp]
  field_simp

lemma mixedSlopePolynomial_natDegree_le (d : ℕ) (c : ℕ → ℝ) :
    (mixedSlopePolynomial d c).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

end
end PiExponent.NumericalAmpleness

end OAI
