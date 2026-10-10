import OAI.NumberTheory.Ostmann.Conclusion.SourcePermutation
import OAI.NumberTheory.Ostmann.Construction.InitialSourceFamily
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion
open Construction

abbrev BulkPosition (T : List SourceSlot) := {i : Fin T.length // T[i].role=.bulk}

def bulkPositionPermutation (T : List SourceSlot) (σ : Equiv.Perm (BulkPosition T)) :
    Equiv.Perm (Fin T.length) := Equiv.Perm.ofSubtype σ

theorem bulkPositionPermutation_source (sources : SourceFamily) (T : List SourceSlot)
    (bulk : PrimeSource) (hbulk : ∀i : BulkPosition T, sources T[i.val].origin=bulk)
    (σ : Equiv.Perm (BulkPosition T)) (i : Fin T.length) :
    sources T[bulkPositionPermutation T σ i].origin=sources T[i].origin := by
  change sources (T.get (Equiv.Perm.ofSubtype σ i)).origin = sources (T.get i).origin
  by_cases hi : T[i].role = .bulk
  · rw [Equiv.Perm.ofSubtype_apply_of_mem σ hi]
    exact (hbulk (σ ⟨i,hi⟩)).trans (hbulk ⟨i,hi⟩).symm
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem σ hi]

def bulkAssignmentPermutation (sources : SourceFamily) (T : List SourceSlot)
    (bulk : PrimeSource) (hbulk : ∀i : BulkPosition T, sources T[i.val].origin=bulk)
    (σ : Equiv.Perm (BulkPosition T)) : SourceAssignment sources T ≃ SourceAssignment sources T :=
  sourceAssignmentPermutation sources T (bulkPositionPermutation T σ)
    (bulkPositionPermutation_source sources T bulk hbulk σ)

theorem bulkAssignmentPermutation_mass (sources : SourceFamily) (T : List SourceSlot)
    (bulk : PrimeSource) (hbulk : ∀i : BulkPosition T, sources T[i.val].origin=bulk)
    (σ : Equiv.Perm (BulkPosition T)) (x : SourceAssignment sources T) :
    (assignmentPrior sources T).mass (bulkAssignmentPermutation sources T bulk hbulk σ x)=
      (assignmentPrior sources T).mass x :=
  sourceAssignmentPermutation_mass _ _ _ _ _

theorem initial_bulk_origin_lt {m k : ℕ} {q : SourceSlot}
    (hq : q∈Template.initial m k) (hr : q.role=.bulk) : q.origin < m := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (InitialCoordinatesTemplate.initialRoles_bulk_iff m k i).mp hr

theorem current_bulk_source (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (i : BulkPosition (Template.current (Template.initial (2*b) k) l)) :
    initialSourceFamily b k bulk top comp
      ((Template.current (Template.initial (2*b) k) l)[i.val].origin)=bulk := by
  apply initialSourceValue_bulk
  exact initial_bulk_origin_lt
    (Template.mem_current_mem_seed (List.getElem_mem _)) i.property

def currentBulkAssignmentPermutation (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (BulkPosition (Template.current (Template.initial (2*b) k) l))) :
    SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l) ≃
      SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l) :=
  bulkAssignmentPermutation _ _ bulk (current_bulk_source b k l bulk top comp) σ

end Ostmann.Conclusion

end

end OAI
