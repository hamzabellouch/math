import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobi

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem rightJacobi_initial_abs_le_length (n N : ℕ) :
    |∑ m ∈ Finset.range N, rightJacobi n m| ≤ (N : ℤ) := by
  calc
    |∑ m ∈ Finset.range N, rightJacobi n m| ≤ ∑ m ∈ Finset.range N, |rightJacobi n m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.range N, (1 : ℤ) :=
      Finset.sum_le_sum (fun m hm => rightJacobi_abs_le_one n m)
    _ = N := by simp

theorem jacobi_nat_prod {α : Type*} (I : Finset α) (n : α → ℕ) (m : ℕ) :
    jacobiSym ((∏ i ∈ I, n i : ℕ) : ℤ) m = ∏ i ∈ I, jacobiSym (n i : ℤ) m := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, jacobiSym.mul_left, ih]

theorem odd_jacobi_product_correlation_bound {α : Type*} [Fintype α]
    (n : α → ℕ) (hn : ∀ i, 0 < n i) (N : ℕ) :
    |∑ m ∈ (Finset.range N).filter Odd, ∏ i, jacobiSym (n i : ℤ) m| ≤
      if IsSquare (∏ i, n i) then (N : ℤ) else 4 * (∏ i, n i : ℕ) := by
  classical
  have hprod : 0 < ∏ i, n i := Finset.prod_pos (fun i hi => hn i)
  have hsum : (∑ m ∈ (Finset.range N).filter Odd, ∏ i, jacobiSym (n i : ℤ) m) =
      ∑ m ∈ (Finset.range N).filter Odd, jacobiSym ((∏ i, n i : ℕ) : ℤ) m := by
    apply Finset.sum_congr rfl
    intro m hm
    exact (jacobi_nat_prod Finset.univ n m).symm
  rw [hsum]
  by_cases hs : IsSquare (∏ i, n i)
  · rw [ite_eq_left hs]
    simpa only [rightJacobi, Finset.sum_filter] using rightJacobi_initial_abs_le_length (∏ i, n i) N
  · rw [ite_eq_right hs]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      odd_jacobi_nonsquare_initial_sum_bound hprod hs N

theorem odd_jacobi_product_correlation_bound_real {α : Type*} [Fintype α]
    (n : α → ℕ) (hn : ∀ i, 0 < n i) (N : ℕ) :
    |∑ m ∈ (Finset.range N).filter Odd, ∏ i, (jacobiSym (n i : ℤ) m : ℝ)| ≤
      if IsSquare (∏ i, n i) then (N : ℝ) else 4 * (∏ i, n i : ℕ) := by
  exact_mod_cast odd_jacobi_product_correlation_bound n hn N

end Ostmann.QuadraticCenter

end OAI
