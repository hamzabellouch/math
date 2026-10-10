import OAI.NumberTheory.Ostmann.ZeroDensity.DensityShiftedDivisorEnergy

namespace OAI

/-! # Divisor coefficient energy on a concrete positive block -/

namespace Ostmann

open scoped BigOperators

 theorem density_divisor_block_energy (S : Finset ℕ) (M N : ℕ) (hM : 1 ≤ M)
    (hS : S ⊆ Finset.Icc M N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ n.divisors.card) (σ : ℝ) (hσ : 0 ≤ σ) :
    (∑ n ∈ S, ‖densityVerticalCoeff a σ n‖ ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ (2 * σ) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  calc
    _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 / (M : ℝ) ^ (2 * σ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hMn := (Finset.mem_Icc.mp (hS hn)).1
      have hnp : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hM) hMn
      rw [densityVerticalCoeff_square a σ n hnp]
      apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2) (by positivity)).trans
      exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hMp _)
        (Real.rpow_le_rpow hMp.le (by exact_mod_cast hMn) (by positivity))
    _ = (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ (2 * σ) := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ (2 * σ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨hM.trans (Finset.mem_Icc.mp (hS hn)).1, (Finset.mem_Icc.mp (hS hn)).2⟩
      · intro n _ _
        positivity
    _ ≤ _ := div_le_div_of_nonneg_right (density_divisor_square_sum N) (by positivity)

end Ostmann

end OAI
