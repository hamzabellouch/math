import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceVariables
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicSlots

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState
open Construction Characters.RationalHistory HistorySymbolicSlots

variable {ι : Type*}

structure StateExpr (a : State) (ι : Type*) where
  plus : Expr ι
  minus : Expr ι
  small : Fin a.small.length → Expr ι

def StateExpr.Correct {a : State} (e : StateExpr a ι) (x : ι → ℚ) : Prop :=
  e.plus.RegularAt x ∧ e.plus.rationalEval x = (a.giantPlus:ℚ) ∧
  e.minus.RegularAt x ∧ e.minus.rationalEval x = (a.giantMinus:ℚ) ∧
  HistorySymbolicSlots.Correct x a.small e.small

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

def splitSlots (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) : Fin (hp++hm).length → Expr ι :=
  reorder (History.supported_small_split hs) e.small

def pivotExpr (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) : Expr ι :=
  HistorySymbolicStep.pivot a.frequency left.root.frequency right.root.frequency e.plus e.minus
    (List.ofFn comp) (List.ofFn (leftPart (splitSlots hs e)))
      (List.ofFn (rightPart (splitSlots hs e)))

def leftState (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) : StateExpr left.root ι where
  plus := pivotExpr hs e comp
  minus := e.plus
  small := reorder (History.supported_child_small hs).1.symm
    (append comp (leftPart (splitSlots hs e)))

def rightState (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) : StateExpr right.root ι where
  plus := pivotExpr hs e comp
  minus := e.minus
  small := reorder (History.supported_child_small hs).2.symm
    (append comp (rightPart (splitSlots hs e)))

theorem pivotExpr_correct (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (he : e.Correct x) (hc : HistorySymbolicSlots.Correct x u comp) :
    (pivotExpr hs e comp).RegularAt x ∧ (pivotExpr hs e comp).rationalEval x = (p:ℚ) := by
  have hsplit := correct_reorder (History.supported_small_split hs) e.small he.2.2.2.2
  have hhp := product_correct _ (correct_leftPart _ hsplit)
  have hhm := product_correct _ (correct_rightPart _ hsplit)
  have hu := product_correct comp hc
  exact ⟨HistorySymbolicStep.supported_pivot_regular hs e.plus e.minus _ _ _ x
      he.1 he.2.2.1 hu.1 hhp.1 hhm.1 hu.2,
    HistorySymbolicStep.supported_pivot_eval hs e.plus e.minus _ _ _ x
      he.2.1 he.2.2.2.1 hu.2 hhp.2 hhm.2⟩

theorem leftState_correct (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (he : e.Correct x) (hc : HistorySymbolicSlots.Correct x u comp) :
    (leftState hs e comp).Correct x := by
  obtain ⟨h1,h2,h3,h4⟩ := History.supported_child_giants hs
  have hp := pivotExpr_correct hs e comp x he hc
  have hsplit := correct_reorder (History.supported_small_split hs) e.small he.2.2.2.2
  refine ⟨hp.1,?_,he.1,?_,?_⟩
  · simpa only [h1,leftState] using hp.2
  · simpa only [h3,leftState] using he.2.1
  · exact correct_reorder (History.supported_child_small hs).1.symm _
      (correct_append comp _ hc (correct_leftPart _ hsplit))

theorem rightState_correct (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (he : e.Correct x) (hc : HistorySymbolicSlots.Correct x u comp) :
    (rightState hs e comp).Correct x := by
  obtain ⟨h1,h2,h3,h4⟩ := History.supported_child_giants hs
  have hp := pivotExpr_correct hs e comp x he hc
  have hsplit := correct_reorder (History.supported_small_split hs) e.small he.2.2.2.2
  refine ⟨hp.1,?_,he.2.2.1,?_,?_⟩
  · simpa only [h2,rightState] using hp.2
  · simpa only [h4,rightState] using he.2.2.2.1
  · exact correct_reorder (History.supported_child_small hs).2.symm _
      (correct_append comp _ hc (correct_rightPart _ hsplit))

end Ostmann.Arithmetic.HistorySymbolicState

end

end OAI
