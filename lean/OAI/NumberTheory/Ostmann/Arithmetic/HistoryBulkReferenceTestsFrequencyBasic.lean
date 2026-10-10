import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseIndependentReference

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency
open Construction Conclusion Characters HistoryBulkProducts HistoryFrequencyResidues HistoryLinearization
open HistoryPairedFrequencyAverageHaar HistoryBulkSpectatorReferenceRaw CanonicalHistoryLeafBulk

theorem leafValue_frequencyLeaves (M : ℕ) {l : ℕ} (h : History l) (path : Tree.Leaves l) :
    leafValue (frequencyLeaves M h) path =
      Characters.Template.unitConvention (bulkProduct (leafStateAt h path).small : ZMod M) := by
  induction h with
  | leaf a => rfl
  | node a p u hp hm left right il ir =>
    simp only [frequencyLeaves,leafValue,leafStateAt]
    split_ifs
    · exact ir (Fin.tail path)
    · exact il (Fin.tail path)

theorem frequencyLeaves_decode_slots (M : ℕ) (sources : SourceFamily) (m k : ℕ)
    (V : ℕ → ℕ) (l : ℕ) (a : State)
    (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (samples : Fin (2^l)×Fin m → (ZMod M)ˣ)
    (hsamples : ∀u,(samples u:ZMod M)=(bulkSamples sources m k l x u.1 u.2:ZMod M)) :
    frequencyLeaves M (decodeHistory sources (Template.initial m k) V l a c) =
      bulkLeaves m l samples := by
  apply (leafValuesEquiv (ZMod M)ˣ l).symm.injective
  funext path
  change leafValue (frequencyLeaves M _) path = leafValue (bulkLeaves m l samples) path
  rw [leafValue_frequencyLeaves,decodeHistory_leaf_bulkProduct sources m k V l a c x hx,
    leafValue_bulkLeaves]
  apply Units.ext
  have he : (∏i:Fin m,(bulkSamples sources m k l x (orderedLeafIndex l path) i:ZMod M)) =
      ((∏i:Fin m,samples (orderedLeafIndex l path,i)):(ZMod M)ˣ) := by
    change _=(Units.coeHom (ZMod M)) _
    rw [map_prod]
    simp only [Units.coeHom_apply,hsamples]
  rw [Nat.cast_prod,Characters.Template.unitConvention_coe _ (he.symm ▸ Units.isUnit _),he]

theorem frequencyLeaves_decode_slots_permuted (M b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource) (V : ℕ → ℕ)
    (l : ℕ) (a : State)
    (c : HistoryChoices (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    (samples : Fin (2^l)×Fin (2*b) → (ZMod M)ˣ)
    (hsamples : ∀u,(samples u:ZMod M)=
      (bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l x u.1 u.2:ZMod M)) :
    frequencyLeaves M (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a c) =
      bulkLeaves (2*b) l (fun u => samples (σ u)) := by
  apply frequencyLeaves_decode_slots M _ _ _ _ _ _ _ _ hx (samples ∘ σ)
  intro u
  simp only [Function.comp_apply,hsamples,bulkSamples_permuted]

end Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency

end

end OAI
