import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTransferIndex

namespace OAI

/-! The actual tagged row-stage column is the explicit insertion cursor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedRowStage_get_column (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) (t : Fin (3*(width+1)+1)) :
    ((qmaTaggedRowStage width work l r e g)[t.val]'
      (by rw [qmaTaggedRowStage_length]; exact t.isLt)).2 = e (qmaStageCursorFin width e g t) := by
  let cut := qmaGateCut width e g
  let cols := List.ofFn e
  let pre := qmaColumnTransfer l r (cols.take cut)
  let post := qmaColumnTransfer l r (cols.drop cut)
  let ins := (qmaMapGate width work r g,qmaGateArrivalColumn width e g)
  have hc : cut ≤ width+1 := qmaGateCut_le width e g
  have hp : 0 < cut := by dsimp [cut,qmaGateCut]; omega
  have hpre : pre.length = 3*cut := by
    simp only [pre,qmaColumnTransfer_length,List.length_take,cols,List.length_ofFn,Nat.min_eq_left hc]
  have hpost : post.length = 3*(width+1-cut) := by
    simp only [post,qmaColumnTransfer_length,List.length_drop,cols,List.length_ofFn]
  have ht := t.isLt
  have hbound : t.val < ((pre ++ [ins]) ++ post).length := by
    simp only [List.length_append,List.length_singleton,hpre,hpost]
    omega
  change (((pre ++ [ins]) ++ post)[t.val]'hbound).2 = _
  by_cases hb : t.val < 3*cut
  · rw [List.getElem_append_left (by simp only [List.length_append,List.length_singleton,hpre]; omega),
      List.getElem_append_left (by omega)]
    have hsmall : t.val < 3*(cols.take cut).length := by
      simp only [List.length_take,cols,List.length_ofFn,Nat.min_eq_left hc]
      exact hb
    rw [qmaColumnTransfer_get_column l r (cols.take cut) t.val hsmall,List.getElem_take,
      List.getElem_ofFn]
    apply congrArg e
    apply Fin.ext
    simp only [qmaStageCursorFin,Fin.val_mk,qmaStageCursor,cut,hb,ite_true]
  · by_cases he : t.val = 3*cut
    · rw [List.getElem_append_left (by simp only [List.length_append,List.length_singleton,hpre]; omega),
        List.getElem_append_right (by omega)]
      have hz : t.val-pre.length = 0 := by omega
      simp only [hz,List.getElem_cons_zero]
      change qmaGateArrivalColumn width e g = e (qmaStageCursorFin width e g t)
      apply congrArg e
      apply Fin.ext
      simp only [qmaGateArrivalIndex,qmaStageCursorFin,Fin.val_mk,qmaStageCursor]
      change cut-1 = if t.val < 3*cut then _ else if t.val = 3*cut then _ else _
      simp [he,cut]
    · rw [List.getElem_append_right (by simp only [List.length_append,List.length_singleton,hpre]; omega)]
      have hsmall : t.val-(pre ++ [ins]).length < 3*(cols.drop cut).length := by
        simp only [List.length_append,List.length_singleton,hpre,List.length_drop,cols,List.length_ofFn]
        omega
      rw [qmaColumnTransfer_get_column l r (cols.drop cut) _ hsmall,List.getElem_drop,List.getElem_ofFn]
      apply congrArg e
      apply Fin.ext
      simp only [qmaStageCursorFin,Fin.val_mk,List.length_append,List.length_singleton,hpre]
      change cut+(t.val-(3*cut+1))/3 = qmaStageCursor cut t.val
      unfold qmaStageCursor
      simp only [hb,he,ite_false]
      omega

end ContinuumCoulomb

end

end OAI
