import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkDecode
import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkSamples

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion HistoryBulkProducts HistoryLinearization HistoryResidueRegular

theorem decodeHistory_leaf_bulkValues (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (path : Tree.Leaves l) :
    bulkValues (leafStateAt (decodeHistory sources (Template.initial m k) V l a c) path).small=
      List.ofFn (bulkSamples sources m k l x (orderedLeafIndex l path)) := by
  have ha : Template.Matches (Template.current (Template.initial m k) l) a.small := by
    rw [hx]
    exact Template.assignedSlots_matches _ _ _
  rw [decodeHistory_bulkValues _ _ _ _ _ _ _ ha,hx,bulkValues_assignedSlots,bulkBlock_rows]

theorem decodeHistory_leaf_bulkProduct (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (path : Tree.Leaves l) :
    bulkProduct (leafStateAt (decodeHistory sources (Template.initial m k) V l a c) path).small=
      ∏ i, bulkSamples sources m k l x (orderedLeafIndex l path) i := by
  change (bulkValues _).prod=_
  rw [decodeHistory_leaf_bulkValues _ _ _ _ _ _ _ _ hx,List.prod_ofFn]

theorem decodeHistory_leafBulk_coe {q : ℕ} [Fact q.Prime]
    (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hr : Regular q (decodeHistory sources (Template.initial m k) V l a c))
    (path : Tree.Leaves l) :
    (HistoryTreeParameters.leafBulk _ hr path : ZMod q)=
      ∏ i, (bulkSamples sources m k l x (orderedLeafIndex l path) i : ZMod q) := by
  rw [HistoryTreeParameters.leafBulk_coe,decodeHistory_leaf_bulkProduct _ _ _ _ _ _ _ _ hx]
  simp only [Nat.cast_prod]

theorem bulkSamples_permuted (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)) (u : Fin (2^l) × Fin (2*b)) :
    bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l
      (leafBulkAssignmentPermutation b k l bulk top comp σ x) u.1 u.2=
    bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l x (σ u).1 (σ u).2 := by
  exact leafBulkAssignmentPermutation_leaf_val b k l bulk top comp σ x u

theorem decodeHistory_leaf_bulkProduct_permuted (b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ)
    (l : ℕ) (a : State)
    (c : HistoryChoices (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    (path : Tree.Leaves l) :
    bulkProduct (leafStateAt (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a c) path).small=
      ∏ i : Fin (2*b), bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l x
        (σ (orderedLeafIndex l path,i)).1 (σ (orderedLeafIndex l path,i)).2 := by
  refine (decodeHistory_leaf_bulkProduct (initialSourceFamily b k bulk top comp)
    (2*b) k V l a c (leafBulkAssignmentPermutation b k l bulk top comp σ x) hx path).trans ?_
  apply Finset.prod_congr rfl
  intro i hi
  exact bulkSamples_permuted b k l bulk top comp σ x (orderedLeafIndex l path,i)

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
