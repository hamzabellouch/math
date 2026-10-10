import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicLinearity

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCoefficientRegular
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistorySymbolicSlots

variable {ι : Type*}

def StateRegular {a : State} (e : StateExpr a ι) (x : ι → ℚ) : Prop :=
  e.plus.RegularAt x ∧ e.minus.RegularAt x ∧ Correct x a.small e.small

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem child_regular (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (he : StateRegular e x) (hc : Correct x u comp) :
    StateRegular (leftState hs e comp) x ∧ StateRegular (rightState hs e comp) x := by
  have hsplit := correct_reorder (History.supported_small_split hs) e.small he.2.2
  have hhp := product_correct _ (correct_leftPart _ hsplit)
  have hhm := product_correct _ (correct_rightPart _ hsplit)
  have hu := product_correct comp hc
  have hpivot : (pivotExpr hs e comp).RegularAt x :=
    HistorySymbolicStep.supported_pivot_regular hs e.plus e.minus _ _ _ x
      he.1 he.2.1 hu.1 hhp.1 hhm.1 hu.2
  constructor
  · exact ⟨hpivot,he.1,correct_reorder (History.supported_child_small hs).1.symm _
      (correct_append comp _ hc (correct_leftPart _ hsplit))⟩
  · exact ⟨hpivot,he.2.1,correct_reorder (History.supported_child_small hs).2.symm _
      (correct_append comp _ hc (correct_rightPart _ hsplit))⟩

def TreeRegular (x : ι → ℚ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateRegular e x
  | _, .node _ _ _ _ _ left right, e =>
      StateRegular e.1 x ∧ TreeRegular x left e.2.1 ∧ TreeRegular x right e.2.2

theorem encode_regular {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℚ) (he : StateRegular e x)
    (hc : ∀ i, (comp i).RegularAt x ∧
      (comp i).rationalEval x = ((internalSlot h i).value:ℚ)) :
    TreeRegular x h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
      have hu : Correct x u (fun i => comp (Sum.inl i)) := by
        intro i
        simpa only [internalSlot,Sum.elim_inl] using hc (Sum.inl i)
      have hchildren := child_regular hs e _ x he hu
      refine ⟨he,?_,?_⟩
      · exact ihl (History.supported_left hs) _ _ hchildren.1 (fun i => by
          simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i)))
      · exact ihr (History.supported_right hs) _ _ hchildren.2 (fun i => by
          simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i)))

theorem coefficientHistory_regular {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeRegular (rationalSample h) h (coefficientHistory h hs second) := by
  apply encode_regular
  · exact ⟨trivial,trivial,(rootExpr_correct h).2.2.2.2⟩
  · exact compensationExpr_correct h

end Ostmann.Arithmetic.HistoryCoefficientRegular

end

end OAI
