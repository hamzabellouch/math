import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin.PairNormalization
open scoped BigOperators
open Finset Finset.Nat

theorem binomial_convolution (m n k : ℕ) :
    (∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
      ((m+n).choose k : ℝ) := by
  exact_mod_cast (Nat.add_choose_eq m n k).symm

theorem weighted_choose (m i : ℕ) :
    ((i+1 : ℕ) : ℝ) * ((m+1).choose (i+1) : ℝ) =
      ((m+1 : ℕ) : ℝ) * (m.choose i : ℝ) := by
  have h : (i+1) * (m+1).choose (i+1) = (m+1) * m.choose i := by
    simpa only [mul_comm] using (Nat.add_one_mul_choose_eq m i).symm
  exact_mod_cast h

theorem weighted_shift (m k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * f ij.1 ij.2) =
      ((m+1 : ℕ) : ℝ) *
        ∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * f (ij.1+1) ij.2 := by
  rw [sum_antidiagonal_succ]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  dsimp only
  rw [weighted_choose]
  ring

theorem binomial_first_moment (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
      ((m+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  rw [weighted_shift m k (fun _ j => (n.choose j : ℝ)), binomial_convolution]

theorem weighted_shift_right (n k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ) * f ij.1 ij.2) =
      ((n+1 : ℕ) : ℝ) *
        ∑ ij ∈ antidiagonal k, (n.choose ij.2 : ℝ) * f ij.1 (ij.2+1) := by
  rw [sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  dsimp only
  rw [weighted_choose]
  ring

theorem binomial_second_falling (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      ((m+2).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
    ((m+2 : ℕ) : ℝ) * ((m+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  calc
    _ = ∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((m+2).choose ij.1 : ℝ) *
          (((ij.1 : ℝ)-1) * (n.choose ij.2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+2 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1),
          ((m+1).choose ij.1 : ℝ) *
            (((ij.1+1 : ℕ) : ℝ)-1) * (n.choose ij.2 : ℝ) := by
      simpa only [mul_assoc] using weighted_shift (m+1) (k+1)
        (fun i j => ((i : ℝ)-1) * (n.choose j : ℝ))
    _ = ((m+2 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1),
          (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      push_cast
      ring
    _ = _ := by rw [binomial_first_moment]; ring

theorem binomial_cross_moment (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * (ij.2 : ℝ) *
      ((m+1).choose ij.1 : ℝ) * ((n+1).choose ij.2 : ℝ)) =
    ((m+1 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  calc
    _ = ∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) *
          ((ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+1 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1), (m.choose ij.1 : ℝ) *
          ((ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ)) :=
      weighted_shift m (k+1) (fun _ j => (j : ℝ) * ((n+1).choose j : ℝ))
    _ = ((m+1 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1), (ij.2 : ℝ) *
          ((n+1).choose ij.2 : ℝ) * (m.choose ij.1 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) *
          ∑ ij ∈ antidiagonal k, (n.choose ij.2 : ℝ) * (m.choose ij.1 : ℝ)) := by
      rw [weighted_shift_right n k (fun i _ => (m.choose i : ℝ))]
    _ = ((m+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) *
          ∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) := by
      congr 2
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = _ := by rw [binomial_convolution]; ring

theorem difference_decomposition (Q n : ℕ) :
    (∑ ij ∈ antidiagonal n, ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) -
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) := by
  have hfirst : (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      ∑ ij ∈ antidiagonal n, (ij.1 : ℝ) *
        (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ) := by
    calc
      _ = ∑ ij ∈ antidiagonal n, (ij.2 : ℝ) *
          (Q.choose ij.2 : ℝ) * (Q.choose ij.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := sum_antidiagonal_swap (n := n)
        (f := fun ij => (ij.1 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ))
  have hfall : (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      ∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
        (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ) := by
    calc
      _ = ∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
          (Q.choose ij.2 : ℝ) * (Q.choose ij.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := sum_antidiagonal_swap (n := n)
        (f := fun ij => (ij.1 : ℝ) * ((ij.1 : ℝ)-1) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ))
  have hpoint : (∑ ij ∈ antidiagonal n, ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
    (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) -
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  rw [hpoint, hfirst, hfall]
  ring

theorem pair_binomial_moment (m p : ℕ) :
    (∑ ij ∈ antidiagonal (p+1), ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      ((m+2).choose ij.1 : ℝ) * ((m+2).choose ij.2 : ℝ)) =
      2 * ((m+2 : ℕ) : ℝ) * ((2*m+2).choose p : ℝ) := by
  cases p with
  | zero =>
    rw [sum_antidiagonal_succ]
    simp [Nat.choose_one_right]
    ring
  | succ k =>
    rw [difference_decomposition, binomial_second_falling m (m+2) k,
      binomial_first_moment (m+1) (m+2) (k+1), binomial_cross_moment (m+1) (m+1) k]
    have hA : m+(m+2) = 2*m+2 := by omega
    have hB : m+1+(m+2) = (2*m+2)+1 := by omega
    have hC : m+1+(m+1) = 2*m+2 := by omega
    rw [hA, hB, hC]
    have hp : (((2*m+2)+1).choose (k+1) : ℝ) =
        ((2*m+2).choose k : ℝ) + ((2*m+2).choose (k+1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (2*m+2) k
    rw [hp]
    push_cast
    ring

end Laughlin.PairNormalization

end OAI
