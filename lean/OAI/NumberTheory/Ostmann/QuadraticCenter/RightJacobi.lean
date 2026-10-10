import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiNonsquare
import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiPeriodSum

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem rightJacobi_nonsquare_period_sum_eq_zero {n : ℕ}
    (hn : 0 < n) (hns : ¬ IsSquare n) :
    ∑ m ∈ Finset.range (4 * n), rightJacobi n m = 0 := by
  obtain ⟨a, ha, hfa⟩ := exists_nonsquare_right_nonresidue hn hns
  exact residue_sum_zero_of_negative_unit (rightJacobi n) (by omega)
    (rightJacobi_mod n) (rightJacobi_mul n) ha hfa

theorem rightJacobi_nonsquare_initial_sum_bound {n : ℕ}
    (hn : 0 < n) (hns : ¬ IsSquare n) (N : ℕ) :
    |∑ m ∈ Finset.range N, rightJacobi n m| ≤ (4 * n : ℕ) :=
  initial_sum_abs_le_period (rightJacobi n) (by omega) (rightJacobi_mod n)
    (rightJacobi_nonsquare_period_sum_eq_zero hn hns) (rightJacobi_abs_le_one n) N

theorem odd_jacobi_nonsquare_initial_sum_bound {n : ℕ}
    (hn : 0 < n) (hns : ¬ IsSquare n) (N : ℕ) :
    |∑ m ∈ (Finset.range N).filter Odd, jacobiSym (n : ℤ) m| ≤ (4 * n : ℕ) := by
  simpa only [rightJacobi, Finset.sum_filter] using
    rightJacobi_nonsquare_initial_sum_bound hn hns N

theorem odd_jacobi_nonsquare_initial_sum_bound_real {n : ℕ}
    (hn : 0 < n) (hns : ¬ IsSquare n) (N : ℕ) :
    |∑ m ∈ (Finset.range N).filter Odd, (jacobiSym (n : ℤ) m : ℝ)| ≤ 4 * (n : ℝ) := by
  exact_mod_cast odd_jacobi_nonsquare_initial_sum_bound hn hns N

theorem rightJacobi_square_nonneg {n : ℕ} (hs : IsSquare n) (m : ℕ) :
    0 ≤ rightJacobi n m := by
  obtain ⟨a, rfl⟩ := hs
  unfold rightJacobi
  split_ifs
  · rw [Nat.cast_mul, jacobiSym.mul_left]
    exact mul_self_nonneg _
  · exact le_rfl

end Ostmann.QuadraticCenter

end OAI
