import OAI.NumberTheory.JointDickman.Probability.ConditionalFairSplit

namespace OAI

/-! # Regularity loss under the actual conditional fair-split law -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem fair_selected_remaining_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (A : Finset ℕ) (C : ℝ), 0 ≤ C → A ⊆ auxiliaryPrimes B →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
          (∑ R ∈ (auxiliaryPrimes B).powerset,
            if RegularPrimeSet B L τ C R then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) A R) ≤
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
              K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := remaining_prime_regularity_loss hM hκ
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε, hlim, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [hevent] with B hB
  intro A C hC hA hprod
  rw [fairSelectedRemainingMass_bad B L τ C hA, mul_assoc]
  apply mul_le_mul_of_nonneg_left (hB A C hC hA hprod)
  apply bernoulliSubsetMass_nonneg hA
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
  refine ⟨by positivity, ?_⟩
  exact (div_le_one (by linarith only [hp2] : (0 : ℝ) < p)).mpr (by linarith only [hp2])

end JointDickman

end OAI
