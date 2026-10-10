import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairInverse
import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairInversionComponents
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

@[simp] theorem preservesRemainingBands_symm_iff {T : List SourceSlot}
    (e : Equiv.Perm (RemainingIndex T)) :
    PreservesRemainingBands T e.symm ↔ PreservesRemainingBands T e := by
  constructor
  · intro he
    simpa only [Equiv.symm_symm] using he.symm
  · exact PreservesRemainingBands.symm

namespace DiagonalPermutationCount

theorem orderedBulkRestriction_symm {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m)
    (e : Equiv.Perm (RemainingIndex T)) (he : PreservesRemainingBands T e) :
    orderedBulkRestriction E ⟨e.symm,he.symm⟩=(orderedBulkRestriction E ⟨e,he⟩).symm := by
  rfl

@[simp] theorem fullBulkRestriction_symm {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) (e : Equiv.Perm (RemainingIndex T)) :
    fullBulkRestriction E e.symm=(fullBulkRestriction E e).symm := by
  classical
  by_cases he : PreservesRemainingBands T e
  · simp only [fullBulkRestriction,dite_eq_left he,dite_eq_left he.symm]
    exact orderedBulkRestriction_symm E e he
  · have hes : ¬PreservesRemainingBands T e.symm := by simpa only [preservesRemainingBands_symm_iff] using he
    simp only [fullBulkRestriction,dite_eq_right he,dite_eq_right hes]
    rfl

@[simp] theorem remainingBulkPermutation_symm (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (remainingTemplate m k l))) :
    remainingBulkPermutation m k l e.symm=(remainingBulkPermutation m k l e).symm :=
  fullBulkRestriction_symm _ _

end DiagonalPermutationCount
namespace InitialSourceChoice

@[simp] theorem diagonalBadPermutation_symm_iff (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (DiagonalPermutationCount.remainingTemplate m k l))) :
    diagonalBadPermutation m k l e.symm ↔ diagonalBadPermutation m k l e := by
  simp only [diagonalBadPermutation,preservesRemainingBands_symm_iff,
    DiagonalPermutationCount.remainingBulkPermutation_symm,
    Conclusion.transferBadArrangement_symm_iff]

@[simp] theorem diagonalGoodPermutation_symm_iff (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (DiagonalPermutationCount.remainingTemplate m k l))) :
    diagonalGoodPermutation m k l e.symm ↔ diagonalGoodPermutation m k l e := by
  simp only [diagonalGoodPermutation,preservesRemainingBands_symm_iff,
    DiagonalPermutationCount.remainingBulkPermutation_symm,
    Conclusion.transferBadArrangement_symm_iff]

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
