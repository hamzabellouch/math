import OAI.NumberTheory.Ostmann.Construction.AssignmentAppend

namespace OAI

noncomputable section
namespace Ostmann.Construction

theorem assignedSlots_cons (sources : SourceFamily) (q : SourceSlot) (T : List SourceSlot)
    (x : SourceAssignment sources (q::T)) :
    assignedSlots sources (q::T) x =
      {role:=q.role,value:=((assignmentConsEquiv sources q T x).1:ℕ),origin:=q.origin} ::
        assignedSlots sources T (assignmentConsEquiv sources q T x).2 := by
  change List.ofFn (fun i : Fin (T.length+1) =>
    ({role:=(q::T)[i].role,value:=(x i:ℕ),origin:=(q::T)[i].origin}:SmallSlot)) = _
  rw [List.ofFn_succ]
  rfl

theorem assignedSlots_append (sources : SourceFamily) (T U : List SourceSlot)
    (x : SourceAssignment sources (T++U)) :
    assignedSlots sources (T++U) x =
      assignedSlots sources T (assignmentAppendEquiv sources T U x).1 ++
      assignedSlots sources U (assignmentAppendEquiv sources T U x).2 := by
  induction T with
  | nil => rfl
  | cons q T ih =>
    change assignedSlots sources (q::(T++U)) x = _
    rw [assignedSlots_cons sources q (T++U) x]
    rw [ih (assignmentConsEquiv sources q (T++U) x).2]
    simp only [assignmentAppendEquiv,assignmentAppendWeightEquiv,WeightEquiv.trans,
      WeightEquiv.prod,WeightEquiv.refl,WeightEquiv.assoc,WeightEquiv.symm,
      assignmentConsWeightEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
      Equiv.prodAssoc_symm_apply]
    rw [assignedSlots_cons]
    rfl

end Ostmann.Construction

end

end OAI
