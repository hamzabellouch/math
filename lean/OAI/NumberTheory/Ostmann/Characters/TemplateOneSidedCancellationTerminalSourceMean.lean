import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalSourceDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ) (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))

theorem sourceTerminalCoreSlice_eq_analytic (hLS : L≠S)
    (hsep : ∀q∈sourceScheduledShells w (n+1) L,
      ∀r∈sourceScheduledShells w (n+1) S,q.val.Coprime r.val)
    (positive : Bool)
    (hf : sourceTerminalGraph w n σ τ S L=if positive then 2 else -2)
    (hr : sourceTerminalGraph w n σ τ L S=0) (gate : Bool) :
    (sourceTerminalCoordinatePrior w n L).cmean (fun q=>
      (sourceTerminalCoordinatePrior w n S).cmean (fun r=>
        sourceTerminalCoreSlice w n σ τ h h' masks p L S gate q r)) =
    (sourceTerminalCoordinatePrior w n L).cmean (fun q=>
      sourceTerminalMaskedLongFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val *
      ∑r:↥(sourceScheduledShells w (n+1) S),
        ((sourceTerminalCoordinatePrior w n S).mass r.val:ℂ)*
        sourceTerminalMaskedShortFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 r.val.val *
        exposedCharacter (sourceTerminalCharacters w n S r.val.val) positive (q.val:ZMod r.val.val) *
        sourceTerminalCoreAmplitude w n σ τ h h' gate
          (insertCoordinate L (heldPrimeCoordinates p L S r.val) (q.val:ℤ))) := by
  unfold sourceTerminalCoreSlice
  rw [sourceTerminalMaskedPhase_cmean_eq_oneSidedMean w n σ τ h h' masks p L S hLS hsep
    positive hf hr]
  unfold oneSidedMean FinitePrior.cmean
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [insert_heldPrimeCoordinates p L S hLS]
  unfold sourceShortMass sourceTerminalCoordinatePrior
  ring

end
end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
