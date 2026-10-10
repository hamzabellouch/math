import OAI.NumberTheory.Ostmann.Characters.TemplateSourcePivotLossActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Filter InitialCharacterScale

theorem exists_sourcePivotLoss_threshold (β : ℝ) :
    ∃k0 : ℕ, ∀k : ℕ, k0 ≤ k → ∀c : ℝ, 0 < c →
      ∀ᶠ L : ℝ in atTop,
        (∀j : ℕ, 0 ≤ sourcePivotLoss β k L j) ∧
        (∀n : ℕ, n ≤ k →
          (∑j∈Finset.range n,(sourcePivotLoss β k L j+Real.log 2)) ≤ (wordSize k L : ℝ)) ∧
        (∀ (d : Decomposition) (E : Finset ℕ) (δ α ρ γ c₀ BD : ℝ),
          ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀)
            (w : FixedConfigurationWitness s c BD),
          ∀j : ℕ, ∀hj : j<k,
            sourcePivotNormalization w j hj ≤ Real.exp (sourcePivotLoss β k L j)) := by
  obtain ⟨k0,hk0⟩ := eventually_atTop.mp (eventually_sourcePivotLoss_budget β)
  refine ⟨k0,?_⟩
  intro k hk c hc
  filter_upwards [hk0 k hk,eventually_ge_atTop (0 : ℝ),eventually_ge_atTop (-Real.log c)]
    with L hbudget hL hLc
  refine ⟨fun j=>sourcePivotLoss_nonneg β k hL j,hbudget,?_⟩
  intro d E δ α ρ γ c₀ BD s w j hj
  exact sourcePivotNormalization_le_loss w hc hL hLc j hj

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
