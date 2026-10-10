import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicLinearity

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFieldLinearity
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicEncoding
open HistoryOccurrenceVariables HistorySymbolicLinearity

variable {ι K : Type*} [Field K]

theorem pivot_fieldEval (s v w : ℤ) (plus minus : Expr ι)
    (u hp hm : List (Expr ι)) (x : ι → K) :
    (HistorySymbolicStep.pivot s v w plus minus u hp hm).fieldEval x =
      ((v:K)*(minus.fieldEval x*(HistorySymbolicStep.product hm).fieldEval x) -
        (w:K)*(plus.fieldEval x*(HistorySymbolicStep.product hp).fieldEval x)) /
        ((s:K)*(HistorySymbolicStep.product u).fieldEval x) := rfl

def StateLinear (x : ι → K) (X Y : K) {a : State}
    (e c d : StateExpr a ι) : Prop :=
  e.plus.fieldEval x = c.plus.fieldEval x*X+d.plus.fieldEval x*Y ∧
  e.minus.fieldEval x = c.minus.fieldEval x*X+d.minus.fieldEval x*Y ∧
  c.small = e.small ∧ d.small = e.small

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem pivotExpr_linear
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e c d : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (x : ι → K) (X Y : K) (he : StateLinear x X Y e c d) :
    (pivotExpr hs e comp).fieldEval x =
      (pivotExpr hs c comp).fieldEval x*X+(pivotExpr hs d comp).fieldEval x*Y := by
  simp only [pivotExpr,pivot_fieldEval,splitSlots,he.2.2.1,he.2.2.2]
  rw [he.1,he.2.1]
  simp only [div_eq_mul_inv]
  ring

theorem child_linear
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e c d : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (x : ι → K) (X Y : K) (he : StateLinear x X Y e c d) :
    StateLinear x X Y (leftState hs e comp) (leftState hs c comp) (leftState hs d comp) ∧
    StateLinear x X Y (rightState hs e comp) (rightState hs c comp) (rightState hs d comp) := by
  have hpivot := pivotExpr_linear hs e c d comp x X Y he
  constructor
  · refine ⟨hpivot,he.1,?_,?_⟩ <;> simp only [leftState,splitSlots,he.2.2.1,he.2.2.2]
  · refine ⟨hpivot,he.2.1,?_,?_⟩ <;> simp only [rightState,splitSlots,he.2.2.1,he.2.2.2]

def TreeLinear (x : ι → K) (X Y : K) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → TreeExpr ι h → TreeExpr ι h → Prop
  | _, .leaf _, e, c, d => StateLinear x X Y e c d
  | _, .node _ _ _ _ _ left right, e, c, d =>
      StateLinear x X Y e.1 c.1 d.1 ∧
      TreeLinear x X Y left e.2.1 c.2.1 d.2.1 ∧
      TreeLinear x X Y right e.2.2 c.2.2 d.2.2

theorem encode_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e c d : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → K) (X Y : K)
    (he : StateLinear x X Y e c d) :
    TreeLinear x X Y h (encode V outside h hs e comp)
      (encode V outside h hs c comp) (encode V outside h hs d comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
    have hc := child_linear hs e c d (fun i => comp (Sum.inl i)) x X Y he
    exact ⟨he,ihl (History.supported_left hs) _ _ _ _ hc.1,
      ihr (History.supported_right hs) _ _ _ _ hc.2⟩

theorem symbolicHistory_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (x : Key h → K) :
    TreeLinear x (x (Sum.inl false)) (x (Sum.inl true)) h (symbolicHistory h hs)
      (coefficientHistory h hs false) (coefficientHistory h hs true) := by
  apply encode_linear
  simp [StateLinear,rootExpr,coefficientRoot,Expr.fieldEval]

end Ostmann.Arithmetic.HistoryFieldLinearity

end

end OAI
