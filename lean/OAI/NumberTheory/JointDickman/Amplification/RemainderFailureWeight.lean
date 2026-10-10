import OAI.NumberTheory.JointDickman.Probability.FairSplitPairRegularity

namespace OAI

/-! # Weighted failure estimate on the smooth coefficient support -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weighted_remainder_failure
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ F : Finset ℕ → Finset ℕ → ℝ,
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            0 ≤ F A D) →
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            F A D ≠ 0 → (∏ p ∈ A,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
              (∏ p ∈ D,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)) →
          (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
            F A D*fairRemainingPairFailure B L τ C A D) ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*F A D) := by
  obtain ⟨K,hK,hloss⟩ := fair_remaining_pair_regularity_loss hM
    (by norm_num : (0 : ℝ) < 16/5)
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss] with B hb
  intro C hC F hF hs
  simp_rw [mul_sum]
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  by_cases hz : F A D = 0
  · simp only [hz,zero_mul,mul_zero]
    exact le_rfl
  · have hsize := hs A hA D hD hz
    have hh := mul_le_mul_of_nonneg_left
      (hb A D C hC (mem_powerset.mp hA) (mem_powerset.mp hD) hsize.1 hsize.2) (hF A hA D hD)
    convert hh using 1
    ring

end JointDickman

end OAI
