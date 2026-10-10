import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace PeriodicTilingThree

open Polynomial

theorem polynomial_taylor_coeff_top (P : Polynomial ℝ) (r : ℝ) :
    (taylor r P).coeff P.natDegree = P.leadingCoeff := by
  have hd : (hasseDeriv P.natDegree P).natDegree < 1 := by
    have h := natDegree_hasseDeriv_le P P.natDegree
    omega
  rw [taylor_coeff, eval_eq_sum_range' hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, hasseDeriv_coeff, Nat.choose_self,
    Nat.cast_one, one_mul, Polynomial.leadingCoeff]

theorem polynomial_taylor_coeff_pred (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (r : ℝ) :
    (taylor r P).coeff (P.natDegree - 1) =
      P.coeff (P.natDegree - 1) +
        (P.natDegree : ℝ) * P.leadingCoeff * r := by
  have hd : (hasseDeriv (P.natDegree - 1) P).natDegree < 2 := by
    have h := natDegree_hasseDeriv_le P (P.natDegree - 1)
    omega
  have hs : 1 + (P.natDegree - 1) = P.natDegree := by omega
  have hc : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
    have hs' : P.natDegree - 1 + 1 = P.natDegree := by omega
    simpa only [hs'] using Nat.choose_succ_self_right (P.natDegree - 1)
  rw [taylor_coeff, eval_eq_sum_range' hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, hasseDeriv_coeff,
    Nat.choose_self, Nat.cast_one, one_mul, hs, hc, Polynomial.leadingCoeff]

theorem polynomial_shift_difference_coeff_pred (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (a b : ℝ) :
    (taylor a P - taylor b P).coeff (P.natDegree - 1) =
      (P.natDegree : ℝ) * P.leadingCoeff * (a - b) := by
  rw [coeff_sub, polynomial_taylor_coeff_pred P hP,
    polynomial_taylor_coeff_pred P hP]
  ring

theorem polynomial_shift_difference_natDegree_le (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (a b : ℝ) :
    (taylor a P - taylor b P).natDegree ≤ P.natDegree - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases heq : n = P.natDegree
  · subst n
    rw [coeff_sub, polynomial_taylor_coeff_top, polynomial_taylor_coeff_top,
      sub_self]
  · have hlt : P.natDegree < n := by omega
    have ha : (taylor a P).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)
    have hb : (taylor b P).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)
    rw [coeff_sub, ha, hb, sub_self]

theorem polynomial_shift_difference_degree_irrational (P : Polynomial ℝ)
    (hP : 1 < P.natDegree) (hI : Irrational P.leadingCoeff)
    (h k : ℕ) (hhk : h ≠ k) :
    let D := taylor (h : ℝ) P - taylor (k : ℝ) P
    D.natDegree = P.natDegree - 1 ∧ Irrational D.leadingCoeff := by
  dsimp only
  have hp : 0 < P.natDegree := by omega
  have hdiff : (h : ℤ) - (k : ℤ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hhk
  have hprod : Irrational
      ((P.natDegree : ℝ) * P.leadingCoeff * ((h : ℝ) - (k : ℝ))) := by
    simpa only [Int.cast_sub, Int.cast_natCast] using
      (hI.natCast_mul (Nat.ne_of_gt hp)).mul_intCast hdiff
  have hc := polynomial_shift_difference_coeff_pred P hp (h : ℝ) (k : ℝ)
  have hcn : (taylor (h : ℝ) P - taylor (k : ℝ) P).coeff
      (P.natDegree - 1) ≠ 0 := by
    rw [hc]
    exact hprod.ne_zero
  have hd := natDegree_eq_of_le_of_coeff_ne_zero
    (polynomial_shift_difference_natDegree_le P hp (h : ℝ) (k : ℝ)) hcn
  refine ⟨hd, ?_⟩
  rw [Polynomial.leadingCoeff, hd, hc]
  exact hprod

theorem polynomial_shift_difference_leadingCoeff (P : Polynomial ℝ)
    (hP : 1 < P.natDegree) (hI : Irrational P.leadingCoeff)
    (h k : ℕ) (hhk : h ≠ k) :
    (taylor (h : ℝ) P - taylor (k : ℝ) P).leadingCoeff =
      (P.natDegree : ℝ) * P.leadingCoeff * ((h : ℝ) - (k : ℝ)) := by
  have hd := (polynomial_shift_difference_degree_irrational P hP hI h k hhk).1
  rw [Polynomial.leadingCoeff, hd]
  exact polynomial_shift_difference_coeff_pred P (by omega) (h : ℝ) (k : ℝ)

theorem polynomial_shift_difference_eval (P : Polynomial ℝ) (a b x : ℝ) :
    (taylor a P - taylor b P).eval x = P.eval (x + a) - P.eval (x + b) := by
  rw [eval_sub, taylor_eval, taylor_eval]

end PeriodicTilingThree

end OAI
