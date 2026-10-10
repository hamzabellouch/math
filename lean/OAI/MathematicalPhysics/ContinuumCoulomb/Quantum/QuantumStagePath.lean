import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumStageStep
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCongestion

namespace OAI

/-! Row-labelled stages form bounded-step spatial paths with explicit endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaRowLift {rows width : ℕ} (r : Fin (rows+1)) (ps : List (QMAGate × Fin (width+1))) :
    List (QMAGate × QMAGridCell rows width) := ps.map (fun p => (p.1,(r,p.2)))

def QMAGridTagNear {rows width : ℕ} (p q : QMAGate × QMAGridCell rows width) : Prop :=
  p.2.1.val ≤ q.2.1.val+1 ∧ q.2.1.val ≤ p.2.1.val+1 ∧
    p.2.2.val ≤ q.2.2.val+1 ∧ q.2.2.val ≤ p.2.2.val+1

theorem qmaRowLift_chain {rows width : ℕ} (r : Fin (rows+1))
    (ps : List (QMAGate × Fin (width+1))) (h : ps.IsChain QMALabeledColumnNear) :
    (qmaRowLift r ps).IsChain QMAGridTagNear := by
  apply (List.isChain_map _).mpr
  exact h.imp (fun p q hh => by
    change r.val ≤ r.val+1 ∧ r.val ≤ r.val+1 ∧ p.2.val ≤ q.2.val+1 ∧ q.2.val ≤ p.2.val+1
    exact ⟨by omega,by omega,hh⟩)

def qmaGridStageTags (rows width : ℕ) (r : Fin rows) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : List (QMAGate × QMAGridCell rows width) :=
  qmaRowLift r.castSucc (qmaTaggedRowStage width (qmaGridWork rows width)
    (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g)

theorem qmaGridStageTags_nonempty (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) : qmaGridStageTags rows width r e g ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp only [qmaGridStageTags,qmaRowLift,List.length_map,qmaTaggedRowStage_length,List.length_nil] at hh
  omega

theorem qmaGridStageTags_head (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    (qmaGridStageTags rows width r e g).head?.map Prod.snd = some (r.castSucc,e 0) := by
  let ps := qmaTaggedRowStage width (qmaGridWork rows width)
    (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g
  have hp : 0 < ps.length := by rw [qmaTaggedRowStage_length]; omega
  simp only [qmaGridStageTags,qmaRowLift,List.head?_map,Option.map_map,Function.comp_def]
  rw [List.head?_eq_getElem?,List.getElem?_eq_getElem hp]
  simp only [Option.map_some]
  congr 1
  exact Prod.ext rfl (qmaTaggedRowStage_first_column _ _ _ _ _ _)

theorem qmaGridStageTags_last (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    (qmaGridStageTags rows width r e g).getLast?.map Prod.snd = some (r.castSucc,e (Fin.last width)) := by
  let ps := qmaTaggedRowStage width (qmaGridWork rows width)
    (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g
  have hp : 3*(width+1) < ps.length := by rw [qmaTaggedRowStage_length]; omega
  simp only [qmaGridStageTags,qmaRowLift,List.getLast?_map,Option.map_map,Function.comp_def]
  rw [List.getLast?_eq_getElem?]
  simp only [qmaTaggedRowStage_length,Nat.add_sub_cancel]
  rw [List.getElem?_eq_getElem hp]
  simp only [Option.map_some]
  congr 1
  exact Prod.ext rfl (qmaTaggedRowStage_last_column _ _ _ _ _ _)

theorem qmaGridStageTags_chain (rows width : ℕ) (r : Fin rows) (g : QMAGate) :
    (qmaGridStageTags rows width r (qmaSweepOrder width (rows-1-r.val)) g).IsChain QMAGridTagNear :=
  qmaRowLift_chain _ _ (qmaTaggedRowStage_chain _ _ _ _ _ _)

end ContinuumCoulomb

end

end OAI
