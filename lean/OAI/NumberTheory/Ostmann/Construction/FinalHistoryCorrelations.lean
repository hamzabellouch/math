import OAI.NumberTheory.Ostmann.Construction.TransferHistoryEnergy
import OAI.NumberTheory.Ostmann.Construction.DirectedPrimePhase
import OAI.NumberTheory.Ostmann.Construction.FinalActualPrior

namespace OAI

/-! # The final history sum: diagonal energy and exact pair expansion -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def finalHistorySum {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (T : Finset (FrequencyTree ℤ n)) (s : ℤ)
    (W Θ : FrequencyTree ℤ n → ℂ) : ℂ :=
  ∑ h ∈ historiesAtRoot sys n σ T s, W h * Θ h

/-- Root counting measure and the original assignment prior are retained.
History uniqueness removes cross terms before taking any absolute bounds. -/
theorem final_history_energy {X State : Type*} [Fintype X]
    (sys : TransferHistorySystem State) (n : ℕ) (state : X → State)
    (T : Finset (FrequencyTree ℤ n)) (S : Finset ℤ) (μ : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (W Θ : X → FrequencyTree ℤ n → ℂ)
    (hS : ∀ x h, h ∈ T → ValidTransferHistory sys n (state x) h → frequencyRoot n h ∈ S)
    (hΘ : ∀ x h, h ∈ T → ValidTransferHistory sys n (state x) h → ‖Θ x h‖ ≤ 1) :
    (∑ s ∈ S, ∑ x, μ x * ‖finalHistorySum sys n (state x) T s (W x) (Θ x)‖ ^ 2) ≤
      ∑ x, μ x * ∑ h ∈ T, if ValidTransferHistory sys n (state x) h then ‖W x h‖ ^ 2 else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (transfer_history_phase_energy_le sys n (state x) T S (hS x) (W x) (Θ x) (hΘ x)) (hμ x)

/-- Each term carries its own sharp support, including its root-frequency
condition. This identity is used before applying the one-sided estimate. -/
theorem finite_history_pair_expansion {X H K : Type*} [Fintype X]
    (μ : X → ℝ) (T : Finset H) (U : Finset K) (a : H → X → ℂ) (b : K → X → ℂ) :
    (∑ x, (μ x : ℂ) * ((∑ h ∈ T, a h x) * conj (∑ k ∈ U, b k x))) =
      ∑ h ∈ T, ∑ k ∈ U, ∑ x, (μ x : ℂ) * (a h x * conj (b k x)) := by
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k ∈ U, ∑ h ∈ T, ∑ x, (μ x : ℂ) * (a h x * conj (b k x)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The cost of fixing both finite-depth frequency histories is recorded
explicitly. All arithmetic and coprimality guards stay in the term functions. -/
theorem finite_history_pair_bound {X H K : Type*} [Fintype X]
    (μ : X → ℝ) (T : Finset H) (U : Finset K) (a : H → X → ℂ) (b : K → X → ℂ)
    (E : ℝ) (hpair : ∀ h ∈ T, ∀ k ∈ U,
      ‖∑ x, (μ x : ℂ) * (a h x * conj (b k x))‖ ≤ E) :
    ‖∑ x, (μ x : ℂ) * ((∑ h ∈ T, a h x) * conj (∑ k ∈ U, b k x))‖ ≤
      (T.card : ℝ) * U.card * E := by
  rw [finite_history_pair_expansion]
  calc
    _ ≤ ∑ h ∈ T, ‖∑ k ∈ U, ∑ x, (μ x : ℂ) * (a h x * conj (b k x))‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ T, ∑ _k ∈ U, E := by
      apply Finset.sum_le_sum
      intro h hh
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => hpair h hh k hk)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A same-function pair is precisely the nonnegative diagonal energy. -/
theorem diagonal_pair_eq_energy {X : Type*} [Fintype X]
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (A : X → ℂ) :
    ‖∑ x, (μ x : ℂ) * (A x * conj (A x))‖ = ∑ x, μ x * ‖A x‖ ^ 2 := by
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (sq_nonneg _))]

end Ostmann

end OAI
