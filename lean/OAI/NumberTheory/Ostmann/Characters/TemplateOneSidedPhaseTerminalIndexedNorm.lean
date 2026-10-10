import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateNormInputs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalSplit

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem sourceTerminalCharacters_order
    (i : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (q : PrimeUpTo s.locations.Q) :
    orderOf (sourceTerminalCharacters w n i q.val)=orderOf (s.family.character q) := by
  rw [sourceTerminalCharacters,extendCharacterData_prime,scheduled_sourceCharacterData_order]
  simp only [familyCharacter,q.property,dite_true]

theorem sourceTerminalCharacters_higher_order
    (i : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (q : PrimeUpTo s.locations.Q) (hq : q∈s.locations.primes) :
    2<orderOf (sourceTerminalCharacters w n i q.val) := by
  rw [sourceTerminalCharacters_order]
  exact s.family.higher_order q hq

theorem sourceTerminal_exposedCharacter_ne_one
    (i : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (q : PrimeUpTo s.locations.Q) (hq : q∈s.locations.primes) (positive : Bool) :
    exposedCharacter (sourceTerminalCharacters w n i q.val) positive≠1 :=
  exposedCharacter_ne_one _ (sourceTerminalCharacters_higher_order w n i q hq) positive

theorem sourceTerminalPairedUnary_norm_le {V : ℕ}
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (hroot : h.val.1=h'.val.1)
    (hrange : ∀path f,
      f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k ℓ:ℝ) (n+1) path →
        f≠0 ∧ f.natAbs≤V)
    (i : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (q : PrimeUpTo s.locations.Q) (hq : q∈s.locations.primes) (hV : V<q.val) :
    ‖sourceTerminalPairedUnary w n σ τ h.val.1 h.val.2 h'.val.2 i q.val‖≤1 := by
  let : Fact q.val.Prime := ⟨primeUpTo_prime q⟩
  have hχ : sourceTerminalCharacters w n i q.val≠1 := by
    have ho := sourceTerminalCharacters_higher_order w n i q hq
    intro he
    rw [he,orderOf_one] at ho
    norm_num at ho
  have hζ (a : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
      ‖extendUnitData (sourceScheduledUnits w (n+1)) a q.val‖≤1 := by
    rw [extendUnitData_prime]
    exact (fixedConfiguration_scheduled_unit_norm w (n+1) a q).le
  have ht : HistoryFrequencyUnits q.val (n+1) h.val.1 h.val.2 :=
    historyFrequencyUnits_of_prime_gt_cutoff _ hrange hV [] h
  have hu : HistoryFrequencyUnits q.val (n+1) h.val.1 h'.val.2 := by
    rw [hroot]
    exact historyFrequencyUnits_of_prime_gt_cutoff _ hrange hV [] h'
  exact norm_pairedTerminalUnary_le k (n+1) _ _ _ _ _ _ _ _ i q.val hχ
    (hζ _) (hζ _) hu ht

theorem sourceTerminalFactors_norms_on_sources {V : ℕ}
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (hroot : h.val.1=h'.val.1)
    (hrange : ∀path f,
      f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k ℓ:ℝ) (n+1) path →
        f≠0 ∧ f.natAbs≤V)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (Elong Eshort : Finset (PrimeUpTo s.locations.Q))
    (hfixed : ∀i∈frozenVertices L S,p i∈s.locations.primes ∧ V<(p i).val)
    (hlong : ∀q∈Elong,q∈s.locations.primes ∧ V<q.val)
    (hshort : ∀q∈Eshort,q∈s.locations.primes ∧ V<q.val) :
    (∀q∈Elong,‖sourceTerminalLongFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
    (∀q∈Eshort,‖sourceTerminalShortFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  have hp : ∀i∈frozenVertices L S,(p i).val.Prime := fun i _=>primeUpTo_prime (p i)
  have hν : ∀i∈frozenVertices L S,
      ‖sourceTerminalPairedUnary w n σ τ h.val.1 h.val.2 h'.val.2 i (p i).val‖≤1 := by
    intro i hi
    exact sourceTerminalPairedUnary_norm_le w n σ τ h h' hroot hrange i (p i)
      (hfixed i hi).1 (hfixed i hi).2
  constructor
  · intro q hq
    have hn := norm_indexedLongUnary_le_one (sourceTerminalGraph w n σ τ)
      (fun i=>(p i).val) (sourceTerminalCharacters w n)
      (sourceTerminalPairedUnary w n σ τ h.val.1 h.val.2 h'.val.2) L S hp hν q.val
      (primeUpTo_prime q) (sourceTerminalPairedUnary_norm_le w n σ τ h h' hroot hrange L q
        (hlong q hq).1 (hlong q hq).2)
    rw [sourceTerminalLongFactor,norm_mul]
    exact (mul_le_mul (longPrimeSupportMask_norm_le _ L S q.val) hn
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro q hq
    have hn := norm_indexedShortUnary_le_one (sourceTerminalGraph w n σ τ)
      (fun i=>(p i).val) (sourceTerminalCharacters w n)
      (sourceTerminalPairedUnary w n σ τ h.val.1 h.val.2 h'.val.2) L S hp q.val
      (primeUpTo_prime q) (sourceTerminalPairedUnary_norm_le w n σ τ h h' hroot hrange S q
        (hshort q hq).1 (hshort q hq).2)
    rw [sourceTerminalShortFactor,norm_mul]
    exact (mul_le_mul (shortPrimeSupportMask_norm_le _ L S q.val) hn
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
