import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardR
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionPermutation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardR
open Construction Conclusion HistoryBulkProducts HistoryFrequencyResidues
open HistoryBulkSupportConverse HistoryBulkDiagramParameters HistoryBulkResidueNormSum
open HistoryBulkReferenceTestsFrequency HistoryPairBulkTransport
open HistoryPairedFrequencyAverageHaar HistoryBulkSpectatorReferenceRaw

variable (K b k l : ℕ) (bulk : PrimeSource) (top : Fin 3 → PrimeSource)
  (comp : Fin k → Fin 2 → PrimeSource) (V : ℕ → ℕ) (outside : List ℕ)
local notation "sources" => initialSourceFamily b k bulk top comp
local notation "seed" => Template.initial (2*b) k
local notation "T" => Template.current seed l

theorem source_independentRTest_eq_one_of_supported
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x₀ x : SourceAssignment sources T) (s t : ℤ) (gp gm gp' gm' : ℕ)
    (c e : HistoryChoices sources seed V l)
    (hfixed : ∀i : Fin (T).length,((T).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hs : (assignedHistory sources seed V l s gp gm x₀ c).Supported V outside)
    (hs' : (assignedHistory sources seed V l t gp gm
      (leafBulkAssignmentPermutation b k l bulk top comp σ x₀) e).Supported V outside)
    (hnew : (assignedHistory sources seed V l s gp' gm' x c).Supported V outside)
    (hnew' : (assignedHistory sources seed V l t gp' gm'
      (leafBulkAssignmentPermutation b k l bulk top comp σ x) e).Supported V outside)
    (hx : (assignmentPrior sources T).mass x≠0)
    (hc : choicesMass sources seed V l c≠0)
    (he : choicesMass sources seed V l e≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hle : l≤K) :
    independentRTest K
      (assignedHistory sources seed V l s gp gm x₀ c)
      (assignedHistory sources seed V l t gp gm
        (leafBulkAssignmentPermutation b k l bulk top comp σ x₀) e)
      σ (gp',gm')
      (sourceBulkUnits
        ((pairedFrequencyProduct (assignedHistory sources seed V l s gp gm x₀ c)
          (assignedHistory sources seed V l t gp gm
            (leafBulkAssignmentPermutation b k l bulk top comp σ x₀) e))^(K+2))
        sources (2*b) k l x)=1 := by
  have hfixed' : ∀i : Fin (T).length,T[i].role≠.bulk →
      (leafBulkAssignmentPermutation b k l bulk top comp σ x i:ℕ)=
        (leafBulkAssignmentPermutation b k l bulk top comp σ x₀ i:ℕ) := by
    intro i hi
    change (sourceAssignmentPermutation sources _ _ _ x i).val =
      (sourceAssignmentPermutation sources _ _ _ x₀ i).val
    simp only [sourceAssignmentPermutation_val]
    have hi' := leafBulkPermutation_apply_nonbulk (2*b) k l σ i hi
    exact (congrArg (fun j => (x j).val) hi').trans
      ((hfixed i hi).trans (congrArg (fun j => (x₀ j).val) hi').symm)
  have hx' : (assignmentPrior sources T).mass
      (leafBulkAssignmentPermutation b k l bulk top comp σ x)≠0 := by
    change (assignmentPrior sources T).mass (sourceAssignmentPermutation sources _ _ _ x)≠0
    simpa only [sourceAssignmentPermutation_mass] using hx
  rw [independentRTest_source_eq_reference_of_mass K b k l bulk top comp V
    (assignedHistory sources seed V l s gp gm x₀ c)
    (assignedHistory sources seed V l t gp gm
      (leafBulkAssignmentPermutation b k l bulk top comp σ x₀) e)
    (assignedRoot sources T s gp' gm' x)
    (assignedRoot sources T t gp' gm' (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    c e σ x rfl rfl hs hs' hx hfreq]
  apply decoded_independent_reference_eq_one K sources seed V l
    (assignedRoot sources T s gp' gm' x)
    (assignedRoot sources T t gp' gm' (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    (assignedRoot sources T s gp gm x₀)
    (assignedRoot sources T t gp gm (leafBulkAssignmentPermutation b k l bulk top comp σ x₀))
    c e outside hnew hnew'
    (assignedRoot_matches sources T s gp' gm' x)
    (assignedRoot_matches sources T t gp' gm' _)
    (assignedSlots_source_mass_ne_zero sources T x hx)
    (assignedSlots_source_mass_ne_zero sources T _ hx')
    hc he hfreq rfl rfl rfl rfl
  · exact assignedSlots_erase_eq sources T x x₀ hfixed
  · exact assignedSlots_erase_eq sources T _ _ hfixed'
  · exact hle

end Ostmann.Arithmetic.HistoryBulkReferenceForwardR

end

end OAI
