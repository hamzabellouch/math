import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingSlice
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataModulus
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalPrimeBound
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalMaskedMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale
open DiagonalEstimate ParityActions TemplateOneSidedNumericInputs HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ) (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))

def sourceTerminalCoreAmplitude (gate : Bool)
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℤ) : ℂ :=
  terminalCorePairAmplitude k n (sourceWidth w.configuration (wordSize k ℓ)) (wordSize k ℓ)
    (by rw [sourceWidth_word];omega)
    (fun j=>sourceRecurrenceB w.configuration s.J (gapSchedule BD k ℓ) c j (fun _=>0))
    (fun j=>sourceRecurrenceV BD k ℓ j (fun _=>0))
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k ℓ)) s.J h.val.1 h'.val.1
    σ τ h.val.2 h'.val.2 gate s.locations.X (initialGap BD k ℓ)
    (sourceAtomWidth k c) (configurationProductWidth k c) x

def sourceTerminalCoreSlice
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (gate : Bool) (q r : PrimeUpTo s.locations.Q) : ℂ :=
  sourceTerminalMaskedPhase w n σ τ masks (twoPrimeSample p L S q r) h.val.1 h.val.2 h'.val.2 *
    sourceTerminalCoreAmplitude w n σ τ h h' gate
      (fun i=>((twoPrimeSample p L S q r i).val:ℤ))

theorem sourceTerminalHeldCoordinates_height {Cmod : ℝ} (hCmod : 0 ≤ Cmod)
    (hband : ∀q∈E,α*ℓ ≤ Real.log (Real.log q) ∧ Real.log (Real.log q) ≤ β*ℓ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hp : (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (q r : PrimeUpTo s.locations.Q) (hq : q∈sourceScheduledShells w (n+1) L)
    (hr : r∈sourceScheduledShells w (n+1) S) :
    ∀i,|((insertCoordinate L (heldPrimeCoordinates p L S r) (q.val:ℤ) i:ℤ):ℝ)| ≤
      Real.exp (rowLogHeight Cmod (depthScale k) β ℓ) := by
  apply heldPrimeCoordinates_height p L S q r hCmod
  · intro i
    exact (fixedConfiguration_scheduled_log_bounds w hband (n+1) i (p i)
      (primeProductPrior_mem_of_mass_ne_zero _ (sourceScheduledShells_pos w (n+1)) p hp i)).2
  · exact (fixedConfiguration_scheduled_log_bounds w hband (n+1) L q hq).2
  · exact (fixedConfiguration_scheduled_log_bounds w hband (n+1) S r hr).2

end
end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
