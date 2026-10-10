import OAI.Analysis.Laughlin.Asymptotics.ScalarBudget
import OAI.Analysis.Laughlin.FourBody.Estimate
import OAI.Analysis.Laughlin.Operators.SevenSquareAverage
import OAI.Analysis.Laughlin.ThreeBody.FockBudget

namespace OAI

namespace Laughlin.Fock
open Filter
open scoped BigOperators Topology

theorem physical_fock_budget_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 25 ≤ Q, ∀ x : Space Q,
      sourceKForm Q (by omega) x +
        (1-93527408868499/10^14-deltaFormula Q-10946*(3/10^6)-averagedFourTransferError Q) *
          sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_threeBody_budget_eventually,eventually_ge_atTop 25] with Q h3 h25
  obtain ⟨h15,h3⟩ := h3
  refine ⟨h25,fun x => ?_⟩
  have h3x := h3 x
  change sourceA3Form Q x-deltaFormula Q*sourceFockEnergy Q x ≤ _ at h3x
  have h4 := sourceA4Form_bound Q h25 x
  have hs := sourceFockHamiltonian_normal_square Q (by omega) x
  rw [sourceKForm_decomposition Q h25]
  nlinarith

theorem physical_fock_square_eventually :
    ∀ᶠ Q : ℕ in atTop, ∀ x : Space Q,
      (1/100 : ℝ)*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_fock_budget_eventually,
    eventual_scalar_budget averagedFourTransferError averagedFourTransferError_tendsto] with Q h hs
  obtain ⟨hQ,h⟩ := h
  intro x
  have hE : 0 ≤ sourceFockEnergy Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  have hm := mul_le_mul_of_nonneg_right hs hE
  have hk := sourceKForm_nonneg Q (by omega) x
  have hx := h x
  linarith

theorem physical_fock_square_uniform :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q,
      (1/100 : ℝ)*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  obtain ⟨q,hq⟩ := eventually_atTop.mp physical_fock_square_eventually
  exact ⟨max 25 q,le_max_left _ _,fun Q hQ => hq Q (le_trans (le_max_right _ _) hQ)⟩

end Laughlin.Fock

end OAI
