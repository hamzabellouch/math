import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShapeOrder

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Construction

def leafBulkPermutation (m k l : ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin m)) :
    Equiv.Perm (Fin (Template.current (Template.initial m k) l).length) :=
  bulkPositionPermutation _ ((currentBulkPositionEquiv m k l).symm.permCongr σ)

@[simp] theorem leafBulkPermutation_apply_bulk (m k l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin m))
    (x : BulkPosition (Template.current (Template.initial m k) l)) :
    leafBulkPermutation m k l σ x.val=
      ((currentBulkPositionEquiv m k l).symm (σ (currentBulkPositionEquiv m k l x))).val := by
  unfold leafBulkPermutation bulkPositionPermutation
  rw [Equiv.Perm.ofSubtype_apply_of_mem
    ((currentBulkPositionEquiv m k l).symm.permCongr σ) x.property]
  rfl

@[simp] theorem leafBulkPermutation_apply_leaf (m k l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (x : Fin (2^l) × Fin m) :
    leafBulkPermutation m k l σ ((currentBulkPositionEquiv m k l).symm x).val=
      ((currentBulkPositionEquiv m k l).symm (σ x)).val := by
  rw [leafBulkPermutation_apply_bulk,Equiv.apply_symm_apply]

@[simp] theorem leafBulkPermutation_apply_nonbulk (m k l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin m))
    (i : Fin (Template.current (Template.initial m k) l).length)
    (hi : (Template.current (Template.initial m k) l)[i].role≠.bulk) :
    leafBulkPermutation m k l σ i=i :=
  Equiv.Perm.ofSubtype_apply_of_not_mem _ hi

theorem leafBulkPermutation_source (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (i : Fin (Template.current (Template.initial (2*b) k) l).length) :
    initialSourceFamily b k bulk top comp
      ((Template.current (Template.initial (2*b) k) l)[leafBulkPermutation (2*b) k l σ i].origin)=
      initialSourceFamily b k bulk top comp
      ((Template.current (Template.initial (2*b) k) l)[i].origin) :=
  bulkPositionPermutation_source _ _ bulk (current_bulk_source b k l bulk top comp) _ i

def leafBulkAssignmentPermutation (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b))) :
    SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l) ≃
      SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l) :=
  sourceAssignmentPermutation _ _ (leafBulkPermutation (2*b) k l σ)
    (leafBulkPermutation_source b k l bulk top comp σ)

@[simp] theorem leafBulkAssignmentPermutation_val (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l))
    (i : Fin (Template.current (Template.initial (2*b) k) l).length) :
    (leafBulkAssignmentPermutation b k l bulk top comp σ x i).val=
      (x (leafBulkPermutation (2*b) k l σ i)).val :=
  sourceAssignmentPermutation_val _ _ _ _ _ _

@[simp] theorem leafBulkAssignmentPermutation_leaf_val (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l))
    (u : Fin (2^l) × Fin (2*b)) :
    (leafBulkAssignmentPermutation b k l bulk top comp σ x
      ((currentBulkPositionEquiv (2*b) k l).symm u).val).val=
      (x ((currentBulkPositionEquiv (2*b) k l).symm (σ u)).val).val := by
  rw [leafBulkAssignmentPermutation_val,leafBulkPermutation_apply_leaf]

theorem leafBulkAssignmentPermutation_mass (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l)) :
    (assignmentPrior (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l)).mass
      (leafBulkAssignmentPermutation b k l bulk top comp σ x)=
      (assignmentPrior (initialSourceFamily b k bulk top comp) (Template.current (Template.initial (2*b) k) l)).mass x :=
  sourceAssignmentPermutation_mass _ _ _ _ _

end Ostmann.Conclusion

end

end OAI
