import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion

def bulkSamples (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (b : Fin (2^l)) (i : Fin m) : ℕ :=
  (x ((currentBulkPositionEquiv m k l).symm (b,i)).val).val

theorem assignedSlots_blocks (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l)) :
    assignedSlots sources (Template.current (Template.initial m k) l) x=
      (List.ofFn (fun b : Fin (2^l) => List.ofFn
        (fun i : Fin (bulkLeafTemplate m k l).length =>
          let j := (currentPositionBlockEquiv m k l).symm (b,i)
          ({role := (Template.current (Template.initial m k) l)[j].role,
            value := (x j).val,
            origin := (Template.current (Template.initial m k) l)[j].origin} : SmallSlot)))).flatten := by
  unfold assignedSlots Template.sample
  rw [List.ofFn_congr (current_bulk_block_length m k l),List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  apply congrArg List.ofFn
  funext i
  have he (j : Fin (2^l*(bulkLeafTemplate m k l).length))
      (hj : j.val=b.val*(bulkLeafTemplate m k l).length+i.val) :
      Fin.cast (current_bulk_block_length m k l).symm j=
        (currentPositionBlockEquiv m k l).symm (b,i) := by
    apply Fin.ext
    simpa using hj
  simp only [he]
  congr 1
  apply congrArg (fun j => (x j).val)
  exact he _ rfl

theorem bulkValues_flatten (xs : List (List SmallSlot)) :
    bulkValues xs.flatten=(xs.map bulkValues).flatten := by
  simp only [bulkValues,List.filter_flatten,List.map_flatten,List.map_map]
  rfl

theorem bulkValues_assignedSlots (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l)) :
    bulkValues (assignedSlots sources (Template.current (Template.initial m k) l) x)=
      rows (bulkSamples sources m k l x) := by
  rw [assignedSlots_blocks,bulkValues_flatten,List.map_ofFn]
  unfold rows
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  change bulkValues (List.ofFn (fun i : Fin (bulkLeafTemplate m k l).length =>
    ({role := (Template.current (Template.initial m k) l)[(currentPositionBlockEquiv m k l).symm (b,i)].role,
      value := (x ((currentPositionBlockEquiv m k l).symm (b,i))).val,
      origin := (Template.current (Template.initial m k) l)[(currentPositionBlockEquiv m k l).symm (b,i)].origin} : SmallSlot)))=_
  rw [bulkValues_ofFn_prefix (bulkLeafTemplate_length_ge m k l) _ (by
    intro i
    simp only [Fin.getElem_fin,currentPositionBlockEquiv_get]
    exact bulkLeafTemplate_bulk_iff m k l i)]
  rfl

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
