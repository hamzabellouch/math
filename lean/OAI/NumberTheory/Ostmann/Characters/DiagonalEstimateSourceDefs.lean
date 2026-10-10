import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCodeFactorActual
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateUnitFamily
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateInitialActual
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateNormInputs
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsPivotRange
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsTargets

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)

abbrev sourceScheduledShells (j : ℕ) :=
  scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
    (sourcePrimeShells w.configuration (wordSize k L) w.roles) j

theorem sourceScheduledShells_pos (j : ℕ) : ∀i,0<primeShellMass (sourceScheduledShells w j i) :=
  scheduledPrimeShells_positive k (sourceWidth w.configuration (wordSize k L))
    (sourcePrimeShells w.configuration (wordSize k L) w.roles)
    (sourcePrimeShells_positive w.configuration (wordSize k L) w.roles w.roles_pos) j

abbrev sourceScheduledUnits (j : ℕ) :
    PrimeUnitData (schedule k j) (sourceWidth w.configuration (wordSize k L)) s.locations.Q :=
  scheduledUnitData k (sourceWidth w.configuration (wordSize k L))
    (sourceUnitData w.configuration (wordSize k L) (fun _=>familyPhase s.family)) j

abbrev sourceScheduledCharacters (j : ℕ) :
    PrimeCharacterData (schedule k j) (sourceWidth w.configuration (wordSize k L)) s.locations.Q :=
  scheduledCharacterData k (sourceWidth w.configuration (wordSize k L))
    (sourceCharacterData w.configuration (wordSize k L) (fun _=>familyCharacter s.family)) j

abbrev sourceScheduledCenters (j : ℕ) :
    PrimeTranslationData (schedule k j) (sourceWidth w.configuration (wordSize k L)) s.locations.Q :=
  scheduledTranslationData k (sourceWidth w.configuration (wordSize k L))
    (sourceTranslationData w.configuration (wordSize k L) (fun _=>familyCenter s.family)) j

def sourcePivotRanges (j : ℕ) : Finset ℕ+ :=
  pivotWindow (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j) (sourceAtomWidth k c)

def sourceMatchingAverage (j : ℕ) (hj : j<k)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (A : Finset (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))) : ℝ :=
  unitMatchingAverage k j hj (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j)
    (sourcePivotRanges w j) A

def sourcePreservingAverage (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ) : ℝ :=
  sourceMatchingAverage w j hj B V (codePreservingMatchings w.configuration (wordSize k L) j)

def sourceChangingAverage (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ) : ℝ :=
  sourceMatchingAverage w j hj B V (Finset.univ\codePreservingMatchings w.configuration (wordSize k L) j)

abbrev sourceUnitDiagonal (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ) : ℝ :=
  unitDiagonal k j hj (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j)
    (sourcePivotRanges w j)

theorem sourceUnitDiagonal_partition (j : ℕ) (hj : j<k)
    (B V : (l:ℕ) → State k (l+1) → ℤ) :
    sourceUnitDiagonal w j hj B V = sourcePreservingAverage w j hj B V+
      sourceChangingAverage w j hj B V :=
  unitDiagonal_matching_partition k j hj (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j)
    (sourcePivotRanges w j) _

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
