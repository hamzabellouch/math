import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDisintegration
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceParity

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

abbrev sourceTerminalPermutation (σ : Reassignments k n (wordSize k ℓ)) :=
  prefixConstituentPermutation k n (sourceWidth w.configuration (wordSize k ℓ)) (wordSize k ℓ)
    (by rw [sourceWidth_word]; omega) σ

def sourceTerminalCoordinatePrior
    (i : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
    FinitePrior (PrimeUpTo s.locations.Q) :=
  primeShellPrior (sourceScheduledShells w (n+1) i) (sourceScheduledShells_pos w (n+1) i)

def sourceTerminalPhasePair (σ τ : Reassignments k n (wordSize k ℓ))
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) : ℂ :=
  conj (unitHistoryPhase k (n+1) (sourceWidth w.configuration (wordSize k ℓ))
    (sourceScheduledUnits w (n+1)) (sourceScheduledCharacters w (n+1)) (sourceScheduledCenters w (n+1))
    (constituentAssignment (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ))
      (sourceTerminalPermutation w n σ) x) r t) *
  unitHistoryPhase k (n+1) (sourceWidth w.configuration (wordSize k ℓ))
    (sourceScheduledUnits w (n+1)) (sourceScheduledCharacters w (n+1)) (sourceScheduledCenters w (n+1))
    (constituentAssignment (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ))
      (sourceTerminalPermutation w n τ) x) r u

def sourceTerminalAmplitude (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q) : ℂ :=
  let weight := fun (υ : Reassignments k n (wordSize k ℓ)) (r : ℤ) (t : HistoryReconstruction.Tree (n+1)) =>
    retainedHistoryWeight k B V (canonicalHistoryExtra k (sourcePivotRanges w))
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
        (initialGap BD k ℓ) (configurationProductWidth k c)))
      s.locations.X (initialGap BD k ℓ) (configurationProductWidth k c) (n+1) r
      (constituentSampleState (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ))
        (constituentAssignment (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ))
          (sourceTerminalPermutation w n υ) x)) t
  conj (weight σ h.val.1 h.val.2) * weight τ h'.val.1 h'.val.2

def sourceTerminalKernel (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q) : ℂ :=
  if samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ)) x then
    sourceTerminalPhasePair w n σ τ x h.val.1 h.val.2 h'.val.2 *
      sourceTerminalAmplitude w n B V σ τ h h' x
  else 0

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
