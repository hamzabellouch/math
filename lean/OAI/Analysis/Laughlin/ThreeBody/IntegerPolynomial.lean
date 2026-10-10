import Mathlib.Algebra.Polynomial.Eval.Degree
import OAI.Analysis.Laughlin.Polynomial.SourceIntegerPolynomial

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_general_sum (c z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U c z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) * (c : ℤ)^(p-h) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩,← List.sum_toFinset _ (List.nodup_range.filter _)]
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

noncomputable def weightedIntegerCouplingPolynomial (c z n : ℕ) : Polynomial ℤ :=
  (Polynomial.X-1)^z * (C (c : ℤ)*Polynomial.X+1)^n

theorem weightedIntegerCouplingPolynomial_coeff (c z n p : ℕ) (hp : p ≤ z+n) :
    (weightedIntegerCouplingPolynomial c z n).coeff p = U c z (z+n) p := by
  rw [U_general_sum c z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold weightedIntegerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  rw [hneg,coeff_X_add_C_pow]
  rw [show (C (c : ℤ)*Polynomial.X+1 : Polynomial ℤ)^n = ((Polynomial.X+1)^n).comp (C (c : ℤ)*Polynomial.X) by simp]
  rw [comp_C_mul_X_coeff]
  rw [show (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 by simp,coeff_X_add_C_pow]
  simp
  ring

end Laughlin.Certificate

end OAI
