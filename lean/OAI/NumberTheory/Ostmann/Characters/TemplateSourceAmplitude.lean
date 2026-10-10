import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateScheduledBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter
open DiagonalEstimate
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)
    (B V : (l:ℕ) → State k (l+1) → ℤ)

def sourceAmplitudeSequence (j : ℕ) : ℂ :=
  scheduledUnitAmplitude k (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w 0) (sourceScheduledShells_pos w 0)
    (sourceScheduledUnits w 0) (sourceScheduledCharacters w 0) (sourceScheduledCenters w 0)
    B V (DiagonalEstimate.sourcePivotRanges w)
    (sourceRangeLeafMask k s.J s.locations.X (initialGap BD k L) (configurationProductWidth k c))
    s.locations.X (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (configurationProductWidth k c) j

abbrev SourceTransferBounds (j : ℕ) (hj : j<k) :=
  ScheduledTransferBounds k (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w 0) (sourceScheduledShells_pos w 0)
    (sourceScheduledUnits w 0) (sourceScheduledCharacters w 0) (sourceScheduledCenters w 0)
    B V (DiagonalEstimate.sourcePivotRanges w)
    (sourceRangeLeafMask k s.J s.locations.X (initialGap BD k L) (configurationProductWidth k c))
    s.locations.X (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (configurationProductWidth k c) j hj

theorem sourceAmplitudeSequence_eq (j : ℕ) :
    sourceAmplitudeSequence w B V j =
      unitAmplitude k j (sourceWidth w.configuration (wordSize k L))
        (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
        B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
        (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
          (initialGap BD k L) (configurationProductWidth k c)))
        s.locations.X (initialGap BD k L) (configurationProductWidth k c)
        (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j)
        (sourceScheduledShells w j) (sourceScheduledShells_pos w j) := rfl

theorem sourceUnitDiagonal_eq_scheduled (j : ℕ) (hj : j<k) :
    sourceUnitDiagonal w j hj B V =
      scheduledUnitDiagonal k (sourceWidth w.configuration (wordSize k L))
        (sourceScheduledShells w 0) (sourceScheduledShells_pos w 0)
        (sourceScheduledUnits w 0) (sourceScheduledCharacters w 0) (sourceScheduledCenters w 0)
        B V (DiagonalEstimate.sourcePivotRanges w)
        (sourceRangeLeafMask k s.J s.locations.X (initialGap BD k L) (configurationProductWidth k c))
        s.locations.X (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (configurationProductWidth k c) j hj := rfl

end

theorem eventually_sourceAmplitudeSequence_zero (k : ℕ) (BD : ℝ) (hBD : 0 ≤ BD) (c : ℝ) :
    ∀ᶠ L : ℝ in atTop,∀ (d : Decomposition) (E : Finset ℕ) (δ α β ρ γ c₀ : ℝ),
    ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD),
    ∀ B V : (l:ℕ) → State k (l+1) → ℤ,
      w.amplitude = sourceAmplitudeSequence w B V 0 := by
  filter_upwards [eventually_fixedConfiguration_amplitude_eq k BD hBD c] with L hL
  intro d E δ α β ρ γ c₀ s w B V
  exact hL d E δ α β ρ γ c₀ s w B V (DiagonalEstimate.sourcePivotRanges w)

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
