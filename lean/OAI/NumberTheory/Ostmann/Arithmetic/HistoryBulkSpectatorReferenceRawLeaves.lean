import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawDecode

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction Conclusion Characters HistoryFrequencyResidues HistoryPairedFrequencyAverageHaar
open HistoryBulkProducts HistoryLinearization CanonicalHistoryLeafBulk
variable {q : ℕ} [Fact q.Prime]

theorem rawLeaves_eq_unitConvention {l : ℕ} (h : History l) (path : Tree.Leaves l) :
    rawLeaves q h path=Characters.Template.unitConvention (bulkProduct (leafStateAt h path).small:ZMod q) := by
  induction h with
  | leaf a => rfl
  | node a p u hp hm left right il ir =>
    simp only [rawLeaves,frequencyLeaves,leafValue,leafStateAt]
    split_ifs
    · exact ir (Fin.tail path)
    · exact il (Fin.tail path)

theorem rawLeaves_decode_slots (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (samples : Fin (2^l)×Fin m→(ZMod q)ˣ)
    (hsamples : ∀u,(samples u:ZMod q)=(bulkSamples sources m k l x u.1 u.2:ZMod q))
    (path : Tree.Leaves l) :
    rawLeaves q (decodeHistory sources (Template.initial m k) V l a c) path=
      ∏i,samples (orderedLeafIndex l path,i) := by
  rw [rawLeaves_eq_unitConvention,decodeHistory_leaf_bulkProduct sources m k V l a c x hx]
  apply Units.ext
  have he : (∏i:Fin m,(bulkSamples sources m k l x (orderedLeafIndex l path) i:ZMod q))=
      ((∏i:Fin m,samples (orderedLeafIndex l path,i)):(ZMod q)ˣ) := by
    change _=(Units.coeHom (ZMod q)) _
    rw [map_prod]
    simp only [Units.coeHom_apply,hsamples]
  rw [Nat.cast_prod,Characters.Template.unitConvention_coe _ (he.symm ▸ Units.isUnit _),he]

theorem rawLeaves_decode_slots_permuted (b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ)
    (l : ℕ) (a : State)
    (c : HistoryChoices (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    (samples : Fin (2^l)×Fin (2*b)→(ZMod q)ˣ)
    (hsamples : ∀u,(samples u:ZMod q)=
      (bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l x u.1 u.2:ZMod q))
    (path : Tree.Leaves l) :
    rawLeaves q (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a c) path=
      ∏i,samples (σ (orderedLeafIndex l path,i)) := by
  apply rawLeaves_decode_slots _ _ _ _ _ _ _ _ hx (samples ∘ σ) _ path
  intro u
  simp only [Function.comp_apply,hsamples,bulkSamples_permuted]

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
