import OAI.NumberTheory.Ostmann.Arithmetic.HistoryNumeratorForms

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCoefficientIndependence
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistorySymbolicSlots
open HistoryNumeratorForms

variable {ι : Type*}

def determinant {a : State} (c d : StateExpr a ι) (x : ι → ℚ) : ℚ :=
  c.plus.rationalEval x*d.minus.rationalEval x-d.plus.rationalEval x*c.minus.rationalEval x

def Independent {a : State} (c d : StateExpr a ι) (x : ι → ℚ) : Prop :=
  c.small = d.small ∧ Correct x a.small c.small ∧ determinant c d x ≠ 0

theorem positive_small_product {a : State} (ha : a.Positive) :
    0 < (a.small.map SmallSlot.value).prod := by
  apply List.prod_pos
  intro v hv
  exact ha v (by simp only [State.values,List.mem_cons]; exact Or.inr (Or.inr hv))

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem inherited_products_positive
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    0 < (hp.map SmallSlot.value).prod ∧ 0 < (hm.map SmallSlot.value).prod := by
  have ha := positive_small_product (History.supported_root_positive hs)
  change 0 < (a.small.map SmallSlot.value).prod at ha
  rw [History.supported_small_product_split hs] at ha
  exact ⟨Nat.pos_of_ne_zero (fun h => by simp [h] at ha),
    Nat.pos_of_ne_zero (fun h => by simp [h] at ha)⟩

theorem determinant_left
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (hsmall : c.small = d.small) :
    determinant (leftState hs c comp) (leftState hs d comp) x =
      -((left.root.frequency:ℚ)*
        (HistorySymbolicStep.product (List.ofFn (rightPart (splitSlots hs c)))).rationalEval x /
        ((a.frequency:ℚ)*(HistorySymbolicStep.product (List.ofFn comp)).rationalEval x))*
        determinant c d x := by
  simp only [determinant,leftState,pivotExpr,HistorySymbolicStep.pivot_eval,
    splitSlots,← hsmall,div_eq_mul_inv]
  ring

theorem determinant_right
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (hsmall : c.small = d.small) :
    determinant (rightState hs c comp) (rightState hs d comp) x =
      -((right.root.frequency:ℚ)*
        (HistorySymbolicStep.product (List.ofFn (leftPart (splitSlots hs c)))).rationalEval x /
        ((a.frequency:ℚ)*(HistorySymbolicStep.product (List.ofFn comp)).rationalEval x))*
        determinant c d x := by
  simp only [determinant,rightState,pivotExpr,HistorySymbolicStep.pivot_eval,
    splitSlots,← hsmall,div_eq_mul_inv]
  ring

theorem child_independent
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℚ)
    (he : Independent c d x) (hc : Correct x u comp) :
    Independent (leftState hs c comp) (leftState hs d comp) x ∧
      Independent (rightState hs c comp) (rightState hs d comp) x := by
  have hsplit := correct_reorder (History.supported_small_split hs) c.small he.2.1
  have hhp := product_correct _ (correct_leftPart _ hsplit)
  have hhm := product_correct _ (correct_rightPart _ hsplit)
  have hu := product_correct comp hc
  have hs0 : (a.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero hs
  have hv0 : (left.root.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero (History.supported_left hs)
  have hw0 : (right.root.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero (History.supported_right hs)
  have hu0 : (HistorySymbolicStep.product (List.ofFn comp)).rationalEval x ≠ 0 := by
    rw [hu.2]
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  have hp0 : (HistorySymbolicStep.product
      (List.ofFn (leftPart (splitSlots hs c)))).rationalEval x ≠ 0 := by
    simp only [splitSlots]
    rw [hhp.2]
    exact_mod_cast (inherited_products_positive hs).1.ne'
  have hm0 : (HistorySymbolicStep.product
      (List.ofFn (rightPart (splitSlots hs c)))).rationalEval x ≠ 0 := by
    simp only [splitSlots]
    rw [hhm.2]
    exact_mod_cast (inherited_products_positive hs).2.ne'
  constructor
  · refine ⟨?_,correct_reorder (History.supported_child_small hs).1.symm _
      (correct_append comp _ hc (correct_leftPart _ hsplit)),?_⟩
    · simp only [leftState,splitSlots,he.1]
    · rw [determinant_left hs c d comp x he.1]
      exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hv0 hm0)
        (mul_ne_zero hs0 hu0))) he.2.2
  · refine ⟨?_,correct_reorder (History.supported_child_small hs).2.symm _
      (correct_append comp _ hc (correct_rightPart _ hsplit)),?_⟩
    · simp only [rightState,splitSlots,he.1]
    · rw [determinant_right hs c d comp x he.1]
      exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hw0 hp0)
        (mul_ne_zero hs0 hu0))) he.2.2

def TreeIndependent (x : ι → ℚ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → TreeExpr ι h → Prop
  | _, .leaf _, c, d => Independent c d x
  | _, .node _ _ _ _ _ left right, c, d =>
      Independent c.1 d.1 x ∧ TreeIndependent x left c.2.1 d.2.1 ∧
        TreeIndependent x right c.2.2 d.2.2

theorem encode_independent {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℚ) (he : Independent c d x)
    (hc : ∀ i, (comp i).RegularAt x ∧
      (comp i).rationalEval x = ((internalSlot h i).value:ℚ)) :
    TreeIndependent x h (encode V outside h hs c comp) (encode V outside h hs d comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
      have hu : Correct x u (fun i => comp (Sum.inl i)) := by
        intro i
        simpa only [internalSlot,Sum.elim_inl] using hc (Sum.inl i)
      have hchildren := child_independent hs c d _ x he hu
      refine ⟨he,?_,?_⟩
      · exact ihl (History.supported_left hs) _ _ _ hchildren.1 (fun i => by
          simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i)))
      · exact ihr (History.supported_right hs) _ _ _ hchildren.2 (fun i => by
          simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i)))

theorem coefficientHistory_independent {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeIndependent (rationalSample h) h
      (coefficientHistory h hs false) (coefficientHistory h hs true) := by
  apply encode_independent
  · refine ⟨rfl,(rootExpr_correct h).2.2.2.2,?_⟩
    simp [determinant,coefficientRoot,Expr.rationalEval]
  · exact compensationExpr_correct h

theorem nodeNumerator_row_ne_zero
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (x : ι → ℚ) (he : Independent c d x) :
    (nodeNumerator hs c).rationalEval x ≠ 0 ∨ (nodeNumerator hs d).rationalEval x ≠ 0 := by
  have hsplit := correct_reorder (History.supported_small_split hs) c.small he.2.1
  have hhm := product_correct _ (correct_rightPart _ hsplit)
  have hv0 : (left.root.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero (History.supported_left hs)
  have hm0 : (HistorySymbolicStep.product
      (List.ofFn (rightPart (splitSlots hs c)))).rationalEval x ≠ 0 := by
    simp only [splitSlots]
    rw [hhm.2]
    exact_mod_cast (inherited_products_positive hs).2.ne'
  have hid : c.plus.rationalEval x*(nodeNumerator hs d).rationalEval x -
      d.plus.rationalEval x*(nodeNumerator hs c).rationalEval x =
      (left.root.frequency:ℚ)*(HistorySymbolicStep.product
        (List.ofFn (rightPart (splitSlots hs c)))).rationalEval x*determinant c d x := by
    simp only [nodeNumerator,HistorySymbolicNumerator.numeratorExpr,
      Expr.rationalEval,determinant,splitSlots,← he.1]
    ring
  by_contra hn
  push Not at hn
  rw [hn.1,hn.2,mul_zero,mul_zero,sub_self] at hid
  exact mul_ne_zero (mul_ne_zero hv0 hm0) he.2.2 hid.symm

end Ostmann.Arithmetic.HistoryCoefficientIndependence

end

end OAI
