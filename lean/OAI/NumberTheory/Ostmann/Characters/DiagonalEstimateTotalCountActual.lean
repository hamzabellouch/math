import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCodeFactorActual
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateTotalCount

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HistoryFrequencyBudget
open HistoryFrequencyLabels InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem exists_fixedConfiguration_total_count_constant (k : ℕ) (BD : ℝ)
    (hBD : 0 ≤ BD) :
    ∃ K : ℝ,0 < K ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (d : Decomposition) (E : Finset ℕ) (δ α β ρ γ c₀ c : ℝ),
      ∀ s : SelectedWordSource d E δ L k α β ρ γ c₀,
      ∀ w : FixedConfigurationWitness s c BD, ∀ j : ℕ,j ≤ k →
      (Fintype.card (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)):ℝ)*
        (Fintype.card (SupportedHistory
          (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) j []):ℝ)^2 ≤
        Real.exp (K*L^2) := by
  obtain ⟨K,hK,hbound⟩ := exists_total_count_constant k BD hBD
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with L hL
  intro d E δ α β ρ γ c₀ c s w j hj
  exact hL j hj w.configuration (fixedConfiguration_cell_count w)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
