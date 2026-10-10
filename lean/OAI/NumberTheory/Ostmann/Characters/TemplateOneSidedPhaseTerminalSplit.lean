import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinPointwise
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedSource

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

def sourceTerminalLongFactor (σ τ : Reassignments k n (wordSize k ℓ))
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) (q : ℕ) : ℂ :=
  longPrimeSupportMask (fun i=>(p i).val) L S q *
    indexedLongUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
      (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) L S q

def sourceTerminalShortFactor (σ τ : Reassignments k n (wordSize k ℓ))
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) (q : ℕ) : ℂ :=
  shortPrimeSupportMask (fun i=>(p i).val) L S q *
    indexedShortUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
      (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) L S q

theorem sourceTerminalPhasePair_twoPrime (σ τ : Reassignments k n (wordSize k ℓ))
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (hLS : L≠S) (q v : PrimeUpTo s.locations.Q)
    (hc : Pairwise (fun i j=>(twoPrimeSample p L S q v i).val.Coprime (twoPrimeSample p L S q v j).val))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1))
    (hrev : sourceTerminalGraph w n σ τ L S=0) :
    sourceTerminalPhasePair w n σ τ (twoPrimeSample p L S q v) r t u =
      indexedLongUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
        (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) L S q.val *
      indexedShortUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
        (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ r t u) L S v.val *
      sourceTerminalCharacters w n S v.val q.val ^ sourceTerminalGraph w n σ τ S L := by
  rw [sourceTerminalPhasePair_eq_graph w n σ τ _ hc r t u]
  have hv : (fun i=>(twoPrimeSample p L S q v i).val)=
      twoPrimeAssignment (fun i=>(p i).val) L S q.val v.val := by
    funext i
    exact twoPrimeSample_val p L S q v i
  have hv' := congrArg (fun a : (schedule k (n+1)).Constituent
      (sourceWidth w.configuration (wordSize k ℓ))→ℕ =>
      primeGraphPhase (sourceTerminalGraph w n σ τ) a
        (fun i=>sourceTerminalCharacters w n i (a i))
        (fun i=>sourceTerminalPairedUnary w n σ τ r t u i (a i))) hv
  rw [hv']
  have hself (i : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
      sourceTerminalGraph w n σ τ i i=0 :=
    differenceGraph_self k (n+1) (sourceWidth w.configuration (wordSize k ℓ))
      (sourceTerminalPermutation w n τ) (sourceTerminalPermutation w n σ) i
  exact indexedPrimeGraphPhase_oneSided (sourceTerminalGraph w n σ τ)
    (fun i=>(p i).val) (sourceTerminalCharacters w n)
    (sourceTerminalPairedUnary w n σ τ r t u) L S hLS (hself L) (hself S) hrev q.val v.val

theorem sourceTerminalKernel_twoPrime (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (hLS : L≠S) (q v : PrimeUpTo s.locations.Q) (hqv : q.val.Coprime v.val)
    (positive : Bool)
    (hforward : sourceTerminalGraph w n σ τ S L=if positive then 2 else -2)
    (hrev : sourceTerminalGraph w n σ τ L S=0) :
    sourceTerminalKernel w n B V σ τ h h' (twoPrimeSample p L S q v) =
      sourceTerminalLongFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val *
      sourceTerminalShortFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 v.val *
      exposedCharacter (sourceTerminalCharacters w n S v.val) positive q.val *
      sourceTerminalAmplitude w n B V σ τ h h' (twoPrimeSample p L S q v) := by
  have hg := twoPrimeAssignment_support_indicator_of_coprime (fun i=>(p i).val) L S hLS q.val v.val hqv
  simp only [←twoPrimeSample_val p L S q v] at hg
  by_cases hc : Pairwise (fun i j=>(twoPrimeSample p L S q v i).val.Coprime (twoPrimeSample p L S q v j).val)
  · have hg' : longPrimeSupportMask (fun i=>(p i).val) L S q.val *
        shortPrimeSupportMask (fun i=>(p i).val) L S v.val=1 := by
      simpa only [ite_eq_left hc] using hg.symm
    rw [sourceTerminalKernel,ite_eq_left (show samplePrimeSupport _ _ (twoPrimeSample p L S q v) from hc)]
    rw [sourceTerminalPhasePair_twoPrime w n σ τ p L S hLS q v hc _ _ _ hrev,
      hforward,←exposedCharacter_apply]
    unfold sourceTerminalLongFactor sourceTerminalShortFactor
    calc
      _ = (longPrimeSupportMask (fun i=>(p i).val) L S q.val *
          shortPrimeSupportMask (fun i=>(p i).val) L S v.val) * _ := by rw [hg',one_mul]
      _ = _ := by ring
  · have hg' : longPrimeSupportMask (fun i=>(p i).val) L S q.val *
        shortPrimeSupportMask (fun i=>(p i).val) L S v.val=0 := by
      simpa only [ite_eq_right hc] using hg.symm
    rw [sourceTerminalKernel,ite_eq_right (show ¬samplePrimeSupport _ _ (twoPrimeSample p L S q v) from hc)]
    unfold sourceTerminalLongFactor sourceTerminalShortFactor
    calc
      _ = (longPrimeSupportMask (fun i=>(p i).val) L S q.val *
          shortPrimeSupportMask (fun i=>(p i).val) L S v.val) *
          (indexedLongUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
            (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ h.val.1 h.val.2 h'.val.2) L S q.val *
          indexedShortUnary (sourceTerminalGraph w n σ τ) (fun i=>(p i).val)
            (sourceTerminalCharacters w n) (sourceTerminalPairedUnary w n σ τ h.val.1 h.val.2 h'.val.2) L S v.val *
          exposedCharacter (sourceTerminalCharacters w n S v.val) positive q.val *
          sourceTerminalAmplitude w n B V σ τ h h' (twoPrimeSample p L S q v)) := by rw [hg',zero_mul]
      _ = _ := by ring
end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
