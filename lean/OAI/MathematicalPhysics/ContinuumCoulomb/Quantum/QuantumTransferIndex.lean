import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCursor

namespace OAI

/-! Exact time-to-column indexing for the three-gate transfer blocks. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaColumnTransfer_length {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) : (qmaColumnTransfer l r cols).length = 3*cols.length := by
  have h := congrArg List.length (qmaColumnTransfer_gates l r cols)
  simpa only [List.length_map,qmaTransferGates_length] using h

theorem qmaColumnTransfer_get_column {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) (t : ℕ) (ht : t < 3*cols.length) :
    ((qmaColumnTransfer l r cols)[t]'(by rw [qmaColumnTransfer_length]; exact ht)).2 =
      cols[t/3]'(by omega) := by
  induction cols generalizing t with
  | nil => simp at ht
  | cons a cols ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        cases t with
        | zero => rfl
        | succ t =>
          have ht' : t < 3*cols.length := by simp only [List.length_cons] at ht; omega
          have hd : (t+1+1+1)/3 = t/3+1 := by omega
          change ((qmaColumnTransfer l r cols)[t]'(by rw [qmaColumnTransfer_length]; exact ht')).2 =
            (a::cols)[(t+1+1+1)/3]
          simpa only [hd,List.getElem_cons_succ] using ih t ht'

theorem qmaTaggedRowStage_length (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    (qmaTaggedRowStage width work l r e g).length = 3*(width+1)+1 := by
  have h := congrArg List.length (qmaTaggedRowStage_gates width work l r e g)
  simpa only [List.length_map,qmaRowStage_length] using h

end ContinuumCoulomb

end

end OAI
