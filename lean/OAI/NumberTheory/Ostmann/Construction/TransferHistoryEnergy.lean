import OAI.NumberTheory.Ostmann.Construction.TransferHistorySquare

namespace OAI

/-! # Summed square energy without a history multiplicity loss -/

namespace Ostmann

open scoped BigOperators Classical

/-- Unique histories allow the sum over root-frequency squares to be
exchanged exactly for the sum of individual squared coefficients. -/
theorem transfer_history_energy_eq {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (T : Finset (FrequencyTree ℤ n)) (S : Finset ℤ)
    (hS : ∀ x ∈ T, ValidTransferHistory sys n σ x → frequencyRoot n x ∈ S)
    (c : FrequencyTree ℤ n → ℂ) :
    (∑ s ∈ S, ‖∑ x ∈ historiesAtRoot sys n σ T s, c x‖ ^ 2) =
      ∑ x ∈ T, if ValidTransferHistory sys n σ x then ‖c x‖ ^ 2 else 0 := by
  simp_rw [history_root_square_eq]
  simp only [historiesAtRoot, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hv : ValidTransferHistory sys n σ x
  · simp only [hv, true_and, ite_true]
    rw [Finset.sum_ite_eq S (frequencyRoot n x)]
    simp only [hS x hx hv, ite_true]
  · simp only [hv, false_and, ite_false, Finset.sum_const_zero]

/-- The graph phase is discarded only after the unique-history square is
formed. This is the original squared-weight majorant in the manuscript. -/
theorem transfer_history_phase_energy_le {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (T : Finset (FrequencyTree ℤ n)) (S : Finset ℤ)
    (hS : ∀ x ∈ T, ValidTransferHistory sys n σ x → frequencyRoot n x ∈ S)
    (W Θ : FrequencyTree ℤ n → ℂ)
    (hΘ : ∀ x ∈ T, ValidTransferHistory sys n σ x → ‖Θ x‖ ≤ 1) :
    (∑ s ∈ S, ‖∑ x ∈ historiesAtRoot sys n σ T s, W x * Θ x‖ ^ 2) ≤
      ∑ x ∈ T, if ValidTransferHistory sys n σ x then ‖W x‖ ^ 2 else 0 := by
  rw [transfer_history_energy_eq sys n σ T S hS]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hv : ValidTransferHistory sys n σ x
  · simp only [hv, ite_true, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    calc
      ‖W x‖ * ‖Θ x‖ ≤ ‖W x‖ * 1 := mul_le_mul_of_nonneg_left (hΘ x hx hv) (norm_nonneg _)
      _ = ‖W x‖ := mul_one _
  · simp only [hv, ite_false, le_refl]

end Ostmann

end OAI
