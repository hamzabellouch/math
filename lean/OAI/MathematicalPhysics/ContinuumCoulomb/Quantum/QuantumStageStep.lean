import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumStageIndex
import Mathlib.Data.List.Chain

namespace OAI

/-! Consecutive clock anchors within a stage are neighboring columns. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMALabeledColumnNear {width : ℕ} (p q : QMAGate × Fin (width+1)) : Prop :=
  p.2.val ≤ q.2.val+1 ∧ q.2.val ≤ p.2.val+1

theorem qmaTaggedRowStage_step (width work row : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) (t : Fin (3*(width+1))) :
    QMALabeledColumnNear
      ((qmaTaggedRowStage width work l r (qmaSweepOrder width row) g)[t.val]'
        (by rw [qmaTaggedRowStage_length]; omega))
      ((qmaTaggedRowStage width work l r (qmaSweepOrder width row) g)[t.val+1]'
        (by rw [qmaTaggedRowStage_length]; omega)) := by
  have hstep := qmaStageCursor_step (qmaGateCut width (qmaSweepOrder width row) g) t.val
    (by unfold qmaGateCut; omega)
  change _ ≤ _ ∧ _ ≤ _
  have h0 := qmaTaggedRowStage_get_column width work l r (qmaSweepOrder width row) g t.castSucc
  have h1 := qmaTaggedRowStage_get_column width work l r (qmaSweepOrder width row) g t.succ
  simp only [Fin.val_castSucc] at h0
  simp only [Fin.val_succ] at h1
  rw [h0,h1]
  apply qmaSweepOrder_near
  · change qmaStageCursor _ t.val ≤ qmaStageCursor _ (t.val+1)+1
    omega
  · exact hstep.2

theorem qmaTaggedRowStage_chain (width work row : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) :
    (qmaTaggedRowStage width work l r (qmaSweepOrder width row) g).IsChain QMALabeledColumnNear := by
  apply List.isChain_iff_getElem.mpr
  intro t ht
  have hlt : t < 3*(width+1) := by rw [qmaTaggedRowStage_length] at ht; omega
  exact qmaTaggedRowStage_step width work row l r g ⟨t,hlt⟩

theorem qmaTaggedRowStage_first_column (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    ((qmaTaggedRowStage width work l r e g)[0]'
      (by rw [qmaTaggedRowStage_length]; omega)).2 = e 0 := by
  have h0 := qmaTaggedRowStage_get_column width work l r e g 0
  simp only [Fin.val_zero] at h0
  rw [h0]
  apply congrArg e
  apply Fin.ext
  change qmaStageCursor (qmaGateCut width e g) 0 = 0
  exact qmaStageCursor_zero _ (by unfold qmaGateCut; omega)

theorem qmaTaggedRowStage_last_column (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    ((qmaTaggedRowStage width work l r e g)[3*(width+1)]'
      (by rw [qmaTaggedRowStage_length]; omega)).2 = e (Fin.last width) := by
  have h0 := qmaTaggedRowStage_get_column width work l r e g (Fin.last (3*(width+1)))
  simp only [Fin.val_last] at h0
  rw [h0]
  apply congrArg e
  apply Fin.ext
  simpa only [qmaStageCursorFin,Fin.val_mk,Fin.val_last,Nat.add_sub_cancel] using
    qmaStageCursor_last (width+1) (qmaGateCut width e g)
      (by unfold qmaGateCut; omega) (qmaGateCut_le width e g)

theorem qmaSweepOrder_turn (width row : ℕ) (hr : 0 < row) :
    qmaSweepOrder width row (Fin.last width) = qmaSweepOrder width (row-1) 0 := by
  have h : row%2 = 0 ∨ row%2 = 1 := by omega
  rcases h with h | h
  · have hp : (row-1)%2 = 1 := by omega
    simp [qmaSweepOrder,h,hp]
  · have hp : (row-1)%2 = 0 := by omega
    simp [qmaSweepOrder,h,hp]

end ContinuumCoulomb

end

end OAI
