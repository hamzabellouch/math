import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTaggedStage

namespace OAI

/-! Exact sweep cursor around the inserted logical gate. -/

noncomputable section
namespace ContinuumCoulomb

/-- Three transfer gates per column, with one gate inserted at the previous column. -/
def qmaStageCursor (cut t : ℕ) : ℕ :=
  if t < 3*cut then t/3 else if t = 3*cut then cut-1 else (t-1)/3

theorem qmaStageCursor_lt (n cut t : ℕ) (hc : 0 < cut) (hcn : cut ≤ n)
    (ht : t < 3*n+1) : qmaStageCursor cut t < n := by
  unfold qmaStageCursor
  split_ifs <;> omega

theorem qmaStageCursor_step (cut t : ℕ) (hc : 0 < cut) :
    qmaStageCursor cut t ≤ qmaStageCursor cut (t+1) ∧
      qmaStageCursor cut (t+1) ≤ qmaStageCursor cut t+1 := by
  unfold qmaStageCursor
  split_ifs <;> omega

theorem qmaStageCursor_zero (cut : ℕ) (hc : 0 < cut) : qmaStageCursor cut 0 = 0 := by
  simp [qmaStageCursor,show 0 < 3*cut by omega]

theorem qmaStageCursor_last (n cut : ℕ) (hc : 0 < cut) (hcn : cut ≤ n) :
    qmaStageCursor cut (3*n) = n-1 := by
  unfold qmaStageCursor
  split_ifs <;> omega

def qmaStageCursorFin (width : ℕ) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate)
    (t : Fin (3*(width+1)+1)) : Fin (width+1) :=
  ⟨qmaStageCursor (qmaGateCut width e g) t.val,
    qmaStageCursor_lt _ _ _ (by unfold qmaGateCut; omega) (qmaGateCut_le width e g) t.isLt⟩

theorem qmaSweepOrder_near (width row : ℕ) (i j : Fin (width+1))
    (hij : i.val ≤ j.val+1) (hji : j.val ≤ i.val+1) :
    (qmaSweepOrder width row i).val ≤ (qmaSweepOrder width row j).val+1 ∧
      (qmaSweepOrder width row j).val ≤ (qmaSweepOrder width row i).val+1 := by
  unfold qmaSweepOrder
  split_ifs
  · exact ⟨hij,hji⟩
  · simp only [Fin.revPerm_apply,Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    omega

end ContinuumCoulomb

end

end OAI
