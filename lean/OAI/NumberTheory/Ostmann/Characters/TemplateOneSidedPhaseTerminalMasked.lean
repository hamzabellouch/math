import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinPointwise
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalSplit

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

def sourceTerminalMaskedPhase (σ τ : Reassignments k n (wordSize k ℓ))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) : ℂ :=
  if samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ)) x then
    (∏i,masks i (x i).val)*sourceTerminalPhasePair w n σ τ x r t u else 0

def sourceTerminalMaskedLongFactor (σ τ : Reassignments k n (wordSize k ℓ))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) (q : ℕ) : ℂ :=
  priorJoinLongUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
    (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) masks L S q

def sourceTerminalMaskedShortFactor (σ τ : Reassignments k n (wordSize k ℓ))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) (q : ℕ) : ℂ :=
  priorJoinShortUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
    (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) masks L S q

theorem sourceTerminalMaskedPhase_twoPrime (σ τ : Reassignments k n (wordSize k ℓ))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (hLS : L≠S) (q v : PrimeUpTo s.locations.Q) (hqv : q.val.Coprime v.val)
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) (positive : Bool)
    (hforward : sourceTerminalGraph w n σ τ S L=if positive then 2 else -2)
    (hrev : sourceTerminalGraph w n σ τ L S=0) :
    sourceTerminalMaskedPhase w n σ τ masks (twoPrimeSample p L S q v) r t u =
      sourceTerminalMaskedLongFactor w n σ τ masks p L S r t u q.val *
      sourceTerminalMaskedShortFactor w n σ τ masks p L S r t u v.val *
      exposedCharacter (sourceTerminalCharacters w n S v.val) positive q.val := by
  have hg := twoPrimeAssignment_support_indicator_of_coprime (fun i=>(p i).val) L S hLS q.val v.val hqv
  simp only [←twoPrimeSample_val p L S q v] at hg
  by_cases hc : Pairwise (fun i j=>(twoPrimeSample p L S q v i).val.Coprime (twoPrimeSample p L S q v j).val)
  · have hg' : longPrimeSupportMask (fun i=>(p i).val) L S q.val *
        shortPrimeSupportMask (fun i=>(p i).val) L S v.val=1 := by
      simpa only [ite_eq_left hc] using hg.symm
    rw [sourceTerminalMaskedPhase,ite_eq_left (show samplePrimeSupport _ _ (twoPrimeSample p L S q v) from hc)]
    simp only [twoPrimeSample_val]
    rw [coordinateMaskProduct_twoPrimeAssignment masks (fun i=>(p i).val) L S hLS,
      sourceTerminalPhasePair_twoPrime w n σ τ p L S hLS q v hc r t u hrev,
      hforward,←exposedCharacter_apply]
    unfold sourceTerminalMaskedLongFactor sourceTerminalMaskedShortFactor priorJoinLongUnary priorJoinShortUnary
    calc
      _ = (longPrimeSupportMask (fun i=>(p i).val) L S q.val *
          shortPrimeSupportMask (fun i=>(p i).val) L S v.val) * _ := by rw [hg',one_mul]
      _ = _ := by ring
  · have hg' : longPrimeSupportMask (fun i=>(p i).val) L S q.val *
        shortPrimeSupportMask (fun i=>(p i).val) L S v.val=0 := by
      simpa only [ite_eq_right hc] using hg.symm
    rw [sourceTerminalMaskedPhase,ite_eq_right (show ¬samplePrimeSupport _ _ (twoPrimeSample p L S q v) from hc)]
    unfold sourceTerminalMaskedLongFactor sourceTerminalMaskedShortFactor priorJoinLongUnary priorJoinShortUnary
    calc
      _ = (longPrimeSupportMask (fun i=>(p i).val) L S q.val *
          shortPrimeSupportMask (fun i=>(p i).val) L S v.val) *
          ((longCoordinateMask masks (fun i=>(p i).val) L S q.val * shortCoordinateMask masks S v.val) *
          (indexedLongUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
            (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) L S q.val *
          indexedShortUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
            (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) L S v.val *
          exposedCharacter (sourceTerminalCharacters w n S v.val) positive q.val)) := by rw [hg',zero_mul]
      _ = _ := by ring
end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
