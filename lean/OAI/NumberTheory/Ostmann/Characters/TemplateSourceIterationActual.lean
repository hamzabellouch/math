import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceIteration
import OAI.NumberTheory.Ostmann.Characters.TemplateSourcePivotLoss

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template InitialCharacterScale DiagonalEstimate Filter
attribute [local instance] Classical.propDecidable

theorem exists_sourceAmplitudeSequence_lower_threshold (β : ℝ) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ BD c α B0 : ℝ,
      1 ≤ BD → 0 < c → 0 < α →
      ∀ᶠ L : ℝ in atTop,
        ∀ (d : Decomposition) (E : Finset ℕ) (δ ρ γ c₀ : ℝ),
        (∀ p ∈ E, α * L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β * L) →
        ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀)
          (w : FixedConfigurationWitness s c BD),
        Real.exp (-B0 * (wordSize k L : ℝ)) ≤ ‖w.amplitude‖ →
        (∀ j (hj : j < k), sourceUnitDiagonal w j hj
          (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
          (sourceRecurrenceV BD k L) ≤
          (1 / 2 : ℝ) * Real.exp (-sourcePivotLoss β k L j) *
            Real.exp (-2 * (B0 + 2) * (2 : ℝ)^j * (wordSize k L : ℝ))) →
        ∀ j ≤ k, Real.exp (-(B0 + 2) * (2 : ℝ)^j * (wordSize k L : ℝ)) ≤
          ‖sourceAmplitudeSequence w
            (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
            (sourceRecurrenceV BD k L) j‖ := by
  obtain ⟨k0, hk0⟩ := exists_sourcePivotLoss_threshold β
  refine ⟨k0, ?_⟩
  intro k hk BD c α B0 hBD hc hα
  filter_upwards [hk0 k hk c hc,
    eventually_fixedConfiguration_sourceTransferBounds k BD c α hBD hc hα,
    eventually_sourceAmplitudeSequence_lower k BD (zero_le_one.trans hBD) c]
    with L hloss hbounds hiteration
  intro d E δ ρ γ c₀ hband s w hinitial hdiag
  apply hiteration d E δ α β ρ γ c₀ s w
    (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
    (sourceRecurrenceV BD k L)
    (fun j hj => Classical.choice (hbounds d E δ β ρ γ c₀ hband s w j hj))
    B0 (B0 + 2) (sourcePivotLoss β k L) hloss.1
  · have hbudget := hloss.2.1 k le_rfl
    have hm : 0 ≤ (wordSize k L : ℝ) := Nat.cast_nonneg _
    nlinarith
  · exact hinitial
  · exact hloss.2.2 d E δ α ρ γ c₀ BD s w
  · exact hdiag

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
