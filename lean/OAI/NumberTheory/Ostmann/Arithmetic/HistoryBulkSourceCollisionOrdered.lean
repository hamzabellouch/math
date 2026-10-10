import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionSeparation
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShape

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction Conclusion

theorem assigned_bulk_nodup_of_injective
    (sources : SourceFamily) (T : List SourceSlot) (x : SourceAssignment sources T)
    (hinj : Function.Injective (fun i : BulkPosition T => (x i.val).val)) :
    (((assignedSlots sources T x).filter (fun a => a.role = .bulk)).map SmallSlot.value).Nodup := by
  have hp : (assignedSlots sources T x).Pairwise
      (fun a b => a.role = .bulk → b.role = .bulk → a.value ≠ b.value) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < T.length := by simpa using hi
    have hj' : j < T.length := by simpa using hj
    simp only [assignedSlots, Template.sample, List.getElem_ofFn]
    intro hbi hbj he
    have eq := hinj (a₁:=⟨⟨i,hi'⟩,hbi⟩) (a₂:=⟨⟨j,hj'⟩,hbj⟩) he
    have hv := congrArg (fun q : BulkPosition T => q.val.val) eq
    exact (Nat.ne_of_lt hij) hv
  change (((assignedSlots sources T x).filter (fun a => a.role = .bulk)).map SmallSlot.value).Pairwise (· ≠ ·)
  apply List.pairwise_map.mpr
  apply (hp.filter _).imp_of_mem
  intro a b ha hb hab
  exact hab (by simpa using (List.mem_filter.mp ha).2) (by simpa using (List.mem_filter.mp hb).2)

theorem assigned_bulk_nodup_of_ordered_injective
    (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hinj : Function.Injective (fun u : Fin (2^l) × Fin m =>
      (x ((currentBulkPositionEquiv m k l).symm u).val).val)) :
    (((assignedSlots sources (Template.current (Template.initial m k) l) x).filter
      (fun a => a.role = .bulk)).map SmallSlot.value).Nodup := by
  apply assigned_bulk_nodup_of_injective
  intro i j he
  apply (currentBulkPositionEquiv m k l).injective
  apply hinj
  exact (congrArg (fun q => (x q.val).val) ((currentBulkPositionEquiv m k l).symm_apply_apply i)).trans
    (he.trans (congrArg (fun q => (x q.val).val)
      ((currentBulkPositionEquiv m k l).symm_apply_apply j)).symm)

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
