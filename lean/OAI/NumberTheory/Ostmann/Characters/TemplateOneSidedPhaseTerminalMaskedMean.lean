import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRows
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalMasked

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
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))

theorem sourceTerminalMaskedPhase_cmean_eq_oneSidedMean (hLS : L≠S)
    (hsep : ∀q∈sourceScheduledShells w (n+1) L,
      ∀r∈sourceScheduledShells w (n+1) S,q.val.Coprime r.val)
    (positive : Bool)
    (hforward : sourceTerminalGraph w n σ τ S L=if positive then 2 else -2)
    (hrev : sourceTerminalGraph w n σ τ L S=0)
    (F : PrimeUpTo s.locations.Q→PrimeUpTo s.locations.Q→ℂ) :
    (sourceTerminalCoordinatePrior w n L).cmean (fun q=>
      (sourceTerminalCoordinatePrior w n S).cmean (fun r=>
        sourceTerminalMaskedPhase w n σ τ masks (twoPrimeSample p L S q r) h.val.1 h.val.2 h'.val.2 * F q r)) =
      oneSidedMean (sourceTerminalCoordinatePrior w n L).mass
        (sourceShortMass (sourceScheduledShells w (n+1) S) (sourceScheduledShells_pos w (n+1) S))
        (fun q=>sourceTerminalMaskedLongFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val)
        (fun r:↥(sourceScheduledShells w (n+1) S)=>
          sourceTerminalMaskedShortFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 r.val.val)
        (fun q r=>exposedCharacter (sourceTerminalCharacters w n S r.val.val) positive q.val *
          F q r.val) := by
  unfold sourceTerminalCoordinatePrior
  simp_rw [primeShellPrior_cmean_eq_subtype (sourceScheduledShells w (n+1) S)
    (sourceScheduledShells_pos w (n+1) S)]
  unfold FinitePrior.cmean oneSidedMean
  apply Finset.sum_congr rfl
  intro q hqall
  by_cases hq : q∈sourceScheduledShells w (n+1) L
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hrall
    rw [sourceTerminalMaskedPhase_twoPrime w n σ τ masks p L S hLS q r.val
      (hsep q hq r.val r.property) h.val.1 h.val.2 h'.val.2 positive hforward hrev]
    unfold sourceShortMass
    ring
  · have hz : (primeShellPrior (sourceScheduledShells w (n+1) L)
        (sourceScheduledShells_pos w (n+1) L)).mass q=0 := by
      simp only [primeShellPrior_mass,ite_eq_right hq,zero_div]
    simp only [hz,Complex.ofReal_zero,zero_mul]
end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
