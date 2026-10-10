import OAI.NumberTheory.Ostmann.Characters.SourceTemplateCharacterLaw
import OAI.NumberTheory.Ostmann.Characters.TemplateScheduledIteration
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceAmplitude

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter DiagonalEstimate
attribute [local instance] Classical.propDecidable

abbrev sourcePivotNormalization {d : Decomposition} {E : Finset ℕ}
    {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (j : ℕ) (hj : j<k) : ℝ :=
  scheduledPivotFactor k (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w 0) j hj

theorem eventually_sourceAmplitudeSequence_lower (k : ℕ) (BD : ℝ) (hBD : 0 ≤ BD) (c : ℝ) :
    ∀ᶠ L : ℝ in atTop,∀ (d : Decomposition) (E : Finset ℕ) (δ α β ρ γ c₀ : ℝ),
    ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD),
    ∀ (B V : (l:ℕ) → State k (l+1) → ℤ),
    (∀j (hj:j<k),SourceTransferBounds w B V j hj) →
    ∀ (B0 B1 : ℝ) (loss : ℕ → ℝ), (∀j,0 ≤ loss j) →
    (∑j∈Finset.range k,(loss j+Real.log 2)) ≤ (B1-B0)*(wordSize k L:ℝ) →
    Real.exp (-B0*(wordSize k L:ℝ)) ≤ ‖w.amplitude‖ →
    (∀j (hj:j<k),sourcePivotNormalization w j hj ≤ Real.exp (loss j)) →
    (∀j (hj:j<k),sourceUnitDiagonal w j hj B V ≤
      (1/2:ℝ)*Real.exp (-loss j)*Real.exp (-2*B1*(2:ℝ)^j*(wordSize k L:ℝ))) →
    ∀j≤k,Real.exp (-B1*(2:ℝ)^j*(wordSize k L:ℝ)) ≤ ‖sourceAmplitudeSequence w B V j‖ := by
  have hrate : 0 ≤ BD+20*Real.log (depthScale k) :=
    add_nonneg hBD (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  filter_upwards [eventually_sourceAmplitudeSequence_zero k BD hBD c,
    (TemplateNormAsymptotic.word_tendsto (depthScale_pos k)).eventually_ge_atTop 1] with L hzero hm
  intro d E δ α β ρ γ c₀ s w B V bounds B0 B1 loss hloss hbudget hinitial hfactor hdiag
  apply scheduledUnitAmplitude_lower k (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w 0) (sourceScheduledShells_pos w 0)
    (sourceScheduledUnits w 0) (fixedConfiguration_unit_norm w)
    (sourceScheduledCharacters w 0) (fixedConfiguration_character_nonprincipal w)
    (sourceScheduledCenters w 0) B V (DiagonalEstimate.sourcePivotRanges w)
    (sourceRangeLeafMask k s.J s.locations.X (initialGap BD k L) (configurationProductWidth k c))
    s.locations.X (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (configurationProductWidth k c)
    hrate hm bounds B0 B1 loss hloss hbudget
  · rw [hzero d E δ α β ρ γ c₀ s w B V] at hinitial
    exact hinitial
  · exact hfactor
  · intro j hj
    exact hdiag j hj

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
