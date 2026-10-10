import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicState

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySymbolicState

variable {ι : Type*}

@[reducible] def TreeExpr (ι : Type*) : {l : ℕ} → History l → Type _
  | _, .leaf a => StateExpr a ι
  | _, .node a _ _ _ _ left right =>
      StateExpr a ι × (TreeExpr ι left × TreeExpr ι right)

def TreeCorrect (x : ι → ℚ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => e.Correct x
  | _, .node _ _ _ _ _ left right, e =>
      e.1.Correct x ∧ TreeCorrect x left e.2.1 ∧ TreeCorrect x right e.2.2

def encode (V : ℕ → ℕ) (outside : List ℕ) :
    {l : ℕ} → (h : History l) → h.Supported V outside → StateExpr h.root ι →
      (InternalKey h → Expr ι) → TreeExpr ι h
  | _, .leaf _, _, e, _ => e
  | _, .node _ _ _ _ _ left right, hs, e, comp =>
      (e,
        encode V outside left (History.supported_left hs)
          (leftState hs e (fun i => comp (Sum.inl i)))
          (fun i => comp (Sum.inr (Sum.inl i))),
        encode V outside right (History.supported_right hs)
          (rightState hs e (fun i => comp (Sum.inl i)))
          (fun i => comp (Sum.inr (Sum.inr i))))

theorem encode_correct {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℚ) (he : e.Correct x)
    (hc : ∀ i, (comp i).RegularAt x ∧
      (comp i).rationalEval x = ((internalSlot h i).value:ℚ)) :
    TreeCorrect x h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
      have hu : HistorySymbolicSlots.Correct x u (fun i => comp (Sum.inl i)) := by
        intro i
        simpa only [internalSlot,Sum.elim_inl] using hc (Sum.inl i)
      refine ⟨he,?_,?_⟩
      · exact ihl (History.supported_left hs) _ _
          (leftState_correct hs e _ x he hu) (fun i => by
            simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i)))
      · exact ihr (History.supported_right hs) _ _
          (rightState_correct hs e _ x he hu) (fun i => by
            simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i)))

def rootExpr {l : ℕ} (h : History l) : StateExpr h.root (Key h) where
  plus := .atom (Sum.inl false)
  minus := .atom (Sum.inl true)
  small := fun i => .atom (Sum.inr (Sum.inl i))

def compensationExpr {l : ℕ} (h : History l) (i : InternalKey h) : Expr (Key h) :=
  .atom (Sum.inr (Sum.inr i))

theorem rootExpr_correct {l : ℕ} (h : History l) :
    (rootExpr h).Correct (rationalSample h) := by
  refine ⟨trivial,?_,trivial,?_,?_⟩
  · simp [rootExpr,Expr.rationalEval,rationalSample,integerSample]
  · simp [rootExpr,Expr.rationalEval,rationalSample,integerSample]
  · intro i
    exact ⟨trivial,by simp [rootExpr,Expr.rationalEval,rationalSample,integerSample]⟩

theorem compensationExpr_correct {l : ℕ} (h : History l) (i : InternalKey h) :
    (compensationExpr h i).RegularAt (rationalSample h) ∧
    (compensationExpr h i).rationalEval (rationalSample h) =
      ((internalSlot h i).value:ℚ) := by
  exact ⟨trivial,by simp [compensationExpr,Expr.rationalEval,rationalSample,integerSample]⟩

def symbolicHistory {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) : TreeExpr (Key h) h :=
  encode V outside h hs (rootExpr h) (compensationExpr h)

theorem symbolicHistory_correct {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeCorrect (rationalSample h) h (symbolicHistory h hs) :=
  encode_correct h hs _ _ _ (rootExpr_correct h) (compensationExpr_correct h)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
