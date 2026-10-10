import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedUnary
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalPriorMean

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

def sourceTerminalCharacters := extendCharacterData (sourceScheduledCharacters w (n+1))

def sourceTerminalGraph (σ τ : Reassignments k n (wordSize k ℓ)) :=
  differenceGraph k (n+1) (sourceWidth w.configuration (wordSize k ℓ))
    (sourceTerminalPermutation w n τ) (sourceTerminalPermutation w n σ)

def sourceTerminalPairedUnary (σ τ : Reassignments k n (wordSize k ℓ))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) :=
  pairedTerminalUnary k (n+1) (sourceWidth w.configuration (wordSize k ℓ))
    (sourceTerminalCharacters w n) (extendUnitData (sourceScheduledUnits w (n+1)))
    (sourceTerminalPermutation w n τ) (sourceTerminalPermutation w n σ) r u t

theorem sourceTerminalPhasePair_eq_graph (σ τ : Reassignments k n (wordSize k ℓ))
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hx : Pairwise (fun i v=>(x i).val.Coprime (x v).val))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) :
    let : ∀i,Fact (x i).val.Prime := fun i=>⟨primeUpTo_prime (x i)⟩
    sourceTerminalPhasePair w n σ τ x r t u =
      primeGraphPhase (sourceTerminalGraph w n σ τ) (fun i=>(x i).val)
        (fun i=>sourceTerminalCharacters w n i (x i).val)
        (fun i=>sourceTerminalPairedUnary w n σ τ r t u i (x i).val) := by
  let : ∀i,Fact (x i).val.Prime := fun i=>⟨primeUpTo_prime (x i)⟩
  have hp := unitHistoryPhase_indexed_pair k (n+1) (sourceWidth w.configuration (wordSize k ℓ))
    (sourceTerminalPermutation w n τ) (sourceTerminalPermutation w n σ) x hx
    (sourceScheduledUnits w (n+1)) (sourceScheduledCharacters w (n+1)) (sourceScheduledCenters w (n+1))
    (source_prefix_characters w.configuration (wordSize k ℓ) n _ (familyCharacter s.family) τ)
    (source_prefix_centers w.configuration (wordSize k ℓ) n _ (familyCenter s.family) τ)
    (source_prefix_characters w.configuration (wordSize k ℓ) n _ (familyCharacter s.family) σ)
    (source_prefix_centers w.configuration (wordSize k ℓ) n _ (familyCenter s.family) σ) r u t
  rw [sourceTerminalPhasePair,mul_comm]
  have hg : sourceTerminalGraph w n σ τ =
      (fun i h => permutedGraph (constituentGraph k (n+1)
        (sourceWidth w.configuration (wordSize k ℓ))) (sourceTerminalPermutation w n τ) i h -
        permutedGraph (constituentGraph k (n+1)
        (sourceWidth w.configuration (wordSize k ℓ))) (sourceTerminalPermutation w n σ) i h) := rfl
  rw [hg]
  simpa only [constituentAssignment,Equiv.coe_fn_mk,sourceTerminalCharacters,
    sourceTerminalPairedUnary,pairedTerminalUnary,extendCharacterData_prime,
    extendUnitData_prime,historyUnaryAt_prime] using hp

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
