import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceDisintegration
open Construction Conclusion

theorem coordinateEquiv_permutation
    (sources : SourceFamily) (T : List SourceSlot) (bulk : PrimeSource)
    (hbulk : ∀i : BulkPosition T, sources (T.get i.val).origin = bulk)
    {ι : Type*} (e : BulkPosition T ≃ ι)
    (σ : Equiv.Perm (Fin T.length))
    (hσ : ∀i, sources (T.get (σ i)).origin = sources (T.get i).origin)
    (τ : Equiv.Perm ι)
    (hnonbulk : ∀i : NonbulkPosition T, σ i.val = i.val)
    (hordered : ∀u, σ (e.symm u).val = (e.symm (τ u)).val)
    (x : SourceAssignment sources T) :
    coordinateEquiv sources T bulk hbulk e (sourceAssignmentPermutation sources T σ hσ x) =
      ((coordinateEquiv sources T bulk hbulk e x).1,
        fun u => (coordinateEquiv sources T bulk hbulk e x).2 (τ u)) := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simp only [coordinateEquiv_nonbulk_apply,sourceAssignmentPermutation_val]
    exact congrArg (fun j => (x j).val) (hnonbulk i)
  · funext u
    apply Subtype.ext
    simp only [coordinateEquiv_bulk_val,sourceAssignmentPermutation_val]
    exact congrArg (fun j => (x j).val) (hordered u)

end Ostmann.Arithmetic.HistoryBulkSourceDisintegration

end

end OAI
