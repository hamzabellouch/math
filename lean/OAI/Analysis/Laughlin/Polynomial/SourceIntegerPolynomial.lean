import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import OAI.Analysis.Laughlin.Operators.Certificate

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_one_sum (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U 1 z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩]
  simp only [Int.natCast_one,one_pow,mul_one]
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
  simp only [List.toFinset_filter,List.toFinset_range]
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_filter,Finset.mem_range] at hh ⊢
    omega
  · intro h hh hn
    simp only [Finset.mem_range,Finset.mem_filter,decide_eq_true_eq,not_and] at hh hn
    by_cases hhz : h ≤ z
    · have hbound : ¬ p+z ≤ T+h := hn (by omega)
      rw [Nat.choose_eq_zero_of_lt (by omega : T-z < p-h)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : z < h)]
      simp

noncomputable def integerCouplingPolynomial (z n : ℕ) : Polynomial ℤ := (Polynomial.X-1)^z * (Polynomial.X+1)^n

theorem integerCouplingPolynomial_coeff (z n p : ℕ) (hp : p ≤ z+n) :
    (integerCouplingPolynomial z n).coeff p = U 1 z (z+n) p := by
  rw [U_one_sum z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold integerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  have hpos : (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 := by simp
  rw [hneg,hpos,coeff_X_add_C_pow,coeff_X_add_C_pow]
  simp

end Laughlin.Certificate

end OAI
