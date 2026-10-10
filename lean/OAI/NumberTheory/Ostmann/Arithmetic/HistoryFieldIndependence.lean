import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldLinearity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFieldIndependence
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistorySymbolicSlots
open HistoryNumeratorForms
variable {ι K : Type*} [Field K]

def determinant {a : State} (c d : StateExpr a ι) (x : ι → K) : K :=
  c.plus.fieldEval x*d.minus.fieldEval x-d.plus.fieldEval x*c.minus.fieldEval x

def Independent {a : State} (c d : StateExpr a ι) (x : ι → K) : Prop :=
  c.small = d.small ∧ (∀ j, (c.small j).fieldEval x ≠ 0) ∧ determinant c d x ≠ 0

theorem product_nonzero (es : List (Expr ι)) (x : ι → K)
    (h : ∀ e ∈ es, e.fieldEval x ≠ 0) : (HistorySymbolicStep.product es).fieldEval x ≠ 0 := by
  induction es with
  | nil =>
      simp only [HistorySymbolicStep.product,Expr.fieldEval,Int.cast_one,ne_eq,one_ne_zero,not_false_eq_true]
  | cons e es ih => exact mul_ne_zero (h e (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem product_ofFn_nonzero {n : ℕ} (f : Fin n → Expr ι) (x : ι → K)
    (h : ∀ j, (f j).fieldEval x ≠ 0) :
    (HistorySymbolicStep.product (List.ofFn f)).fieldEval x ≠ 0 := by
  apply product_nonzero
  intro e he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  exact h j

theorem append_nonzero {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι) (x : ι → K)
    (hf : ∀ j, (f j).fieldEval x ≠ 0) (hg : ∀ j, (g j).fieldEval x ≠ 0) :
    ∀ j, (append f g j).fieldEval x ≠ 0 := by
  intro i
  change (Fin.append f g _).fieldEval x ≠ 0
  refine Fin.addCases (motive := fun j : Fin (xs.length+ys.length) =>
    (Fin.append f g j).fieldEval x ≠ 0) ?_ ?_ _
  · intro j
    simpa only [Fin.append_left] using hf j
  · intro j
    simpa only [Fin.append_right] using hg j

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem determinant_left
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → K)
    (hsmall : c.small = d.small) :
    determinant (leftState hs c comp) (leftState hs d comp) x =
      -((left.root.frequency:K)*
        (HistorySymbolicStep.product (List.ofFn (rightPart (splitSlots hs c)))).fieldEval x /
        ((a.frequency:K)*(HistorySymbolicStep.product (List.ofFn comp)).fieldEval x))*
        determinant c d x := by
  simp only [determinant,leftState,pivotExpr,HistoryFieldLinearity.pivot_fieldEval,
    splitSlots,← hsmall,div_eq_mul_inv]
  ring

theorem determinant_right
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → K)
    (hsmall : c.small = d.small) :
    determinant (rightState hs c comp) (rightState hs d comp) x =
      -((right.root.frequency:K)*
        (HistorySymbolicStep.product (List.ofFn (leftPart (splitSlots hs c)))).fieldEval x /
        ((a.frequency:K)*(HistorySymbolicStep.product (List.ofFn comp)).fieldEval x))*
        determinant c d x := by
  simp only [determinant,rightState,pivotExpr,HistoryFieldLinearity.pivot_fieldEval,
    splitSlots,← hsmall,div_eq_mul_inv]
  ring

theorem child_independent
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → K)
    (he : Independent c d x) (hc : ∀ i, (comp i).fieldEval x ≠ 0)
    (hs0 : (a.frequency:K) ≠ 0) (hv0 : (left.root.frequency:K) ≠ 0)
    (hw0 : (right.root.frequency:K) ≠ 0) :
    Independent (leftState hs c comp) (leftState hs d comp) x ∧
      Independent (rightState hs c comp) (rightState hs d comp) x := by
  have hleft : ∀ i, (leftPart (splitSlots hs c) i).fieldEval x ≠ 0 := fun _ => he.2.1 _
  have hright : ∀ i, (rightPart (splitSlots hs c) i).fieldEval x ≠ 0 := fun _ => he.2.1 _
  have hu0 := product_ofFn_nonzero comp x hc
  have hp0 := product_ofFn_nonzero _ x hleft
  have hm0 := product_ofFn_nonzero _ x hright
  constructor
  · refine ⟨?_,fun _ => append_nonzero comp _ x hc hleft _,?_⟩
    · simp only [leftState,splitSlots,he.1]
    · rw [determinant_left hs c d comp x he.1]
      exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hv0 hm0)
        (mul_ne_zero hs0 hu0))) he.2.2
  · refine ⟨?_,fun _ => append_nonzero comp _ x hc hright _,?_⟩
    · simp only [rightState,splitSlots,he.1]
    · rw [determinant_right hs c d comp x he.1]
      exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hw0 hp0)
        (mul_ne_zero hs0 hu0))) he.2.2

theorem nodeNumerator_nonzero
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (c d : StateExpr a ι) (x : ι → K) (he : Independent c d x)
    (hv0 : (left.root.frequency:K) ≠ 0) :
    (nodeNumerator hs c).fieldEval x ≠ 0 ∨ (nodeNumerator hs d).fieldEval x ≠ 0 := by
  have hm0 := product_ofFn_nonzero (rightPart (splitSlots hs c)) x (fun _ => he.2.1 _)
  have hid : c.plus.fieldEval x*(nodeNumerator hs d).fieldEval x -
      d.plus.fieldEval x*(nodeNumerator hs c).fieldEval x =
      (left.root.frequency:K)*(HistorySymbolicStep.product
        (List.ofFn (rightPart (splitSlots hs c)))).fieldEval x*determinant c d x := by
    simp only [nodeNumerator,HistorySymbolicNumerator.numeratorExpr,
      Expr.fieldEval,determinant,splitSlots,← he.1]
    ring
  by_contra hn
  push Not at hn
  rw [hn.1,hn.2,mul_zero,mul_zero,sub_self] at hid
  exact mul_ne_zero (mul_ne_zero hv0 hm0) he.2.2 hid.symm

theorem encode_occurrence_nonzero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → K) (i : InternalKey h)
    (he : Independent c d x)
    (hc : ∀ j, internalLevel h i < internalLevel h j → (comp j).fieldEval x ≠ 0)
    (hf : ∀ s ∈ h.frequencies, (s:K) ≠ 0) :
    (HistoryOccurrenceRows.rows V outside h hs (encode V outside h hs c comp)
      (encode V outside h hs d comp) i).1.fieldEval x ≠ 0 ∨
    (HistoryOccurrenceRows.rows V outside h hs (encode V outside h hs c comp)
      (encode V outside h hs d comp) i).2.fieldEval x ≠ 0 := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      have hroot : (a.frequency:K) ≠ 0 := hf _ (by simp [History.frequencies])
      have hleft : ∀ s ∈ left.frequencies, (s:K) ≠ 0 :=
        fun s hmem => hf s (by simp [History.frequencies,hmem])
      have hright : ∀ s ∈ right.frequencies, (s:K) ≠ 0 :=
        fun s hmem => hf s (by simp [History.frequencies,hmem])
      have hfl : (left.root.frequency:K) ≠ 0 :=
        hleft _ (HistoryHeightBudgetFixed.root_frequency_mem left)
      have hfr : (right.root.frequency:K) ≠ 0 :=
        hright _ (HistoryHeightBudgetFixed.root_frequency_mem right)
      rcases i with i | i
      · exact nodeNumerator_nonzero hs c d x he hfl
      · rcases i with i | i
        · have hu : ∀ j, (comp (Sum.inl j)).fieldEval x ≠ 0 := by
            intro j
            apply hc (Sum.inl j)
            change internalLevel left i < l+1
            exact Nat.lt_succ_of_le (internalLevel_pos_le left i).2
          have hchildren := child_independent hs c d _ x he hu hroot hfl hfr
          exact ihl (History.supported_left hs) _ _ _ i hchildren.1
            (fun j hj => hc (Sum.inr (Sum.inl j)) hj) hleft
        · have hu : ∀ j, (comp (Sum.inl j)).fieldEval x ≠ 0 := by
            intro j
            apply hc (Sum.inl j)
            change internalLevel right i < l+1
            exact Nat.lt_succ_of_le (internalLevel_pos_le right i).2
          have hchildren := child_independent hs c d _ x he hu hroot hfl hfr
          exact ihr (History.supported_right hs) _ _ _ i hchildren.2
            (fun j hj => hc (Sum.inr (Sum.inr j)) hj) hright

theorem canonical_nonzero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) (x : Key h → K)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      internalLevel h i < keyLevel h (Sum.inr j) → x (Sum.inr j) ≠ 0)
    (hf : ∀ s ∈ h.frequencies, (s:K) ≠ 0) :
    (HistoryOccurrenceRows.canonical h hs i).1.fieldEval x ≠ 0 ∨
      (HistoryOccurrenceRows.canonical h hs i).2.fieldEval x ≠ 0 := by
  apply encode_occurrence_nonzero
  · refine ⟨rfl,?_,?_⟩
    · intro j
      apply hx (Sum.inl j)
      exact Nat.lt_succ_of_le (internalLevel_pos_le h i).2
    · simp [determinant,coefficientRoot,Expr.fieldEval]
  · intro j hj
    exact hx (Sum.inr j) hj
  · exact hf

theorem canonical_regular {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) (x : Key h → K)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      internalLevel h i < keyLevel h (Sum.inr j) → x (Sum.inr j) ≠ 0)
    (hf : ∀ s ∈ h.frequencies, (s:K) ≠ 0) :
    (HistoryOccurrenceRows.canonical h hs i).1.FieldRegularAt x ∧
      (HistoryOccurrenceRows.canonical h hs i).2.FieldRegularAt x := by
  classical
  have ha := HistoryOccurrenceRows.canonical_above h hs i
  have hsafe := HistoryOccurrenceRows.canonical_safe h hs i
  have hfree := HistoryOccurrenceRows.rows_above h hs _ _
    (HistoryCoefficientBounds.rootFreeLevel h)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs false)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs true) i
  have hunit : ∀ e : Expr (Key h),
      HistorySymbolicScope.Above (keyLevel h) (internalLevel h i) e →
      HistorySymbolicScope.Above (HistoryCoefficientBounds.rootFreeLevel h) (internalLevel h i) e →
      ∀ j ∈ e.atoms, x j ≠ 0 := by
    intro e he hfree j hj
    rcases j with b | j
    · have hb := HistorySymbolicScope.above_atoms e hfree (Sum.inl b) hj
      exact False.elim (Nat.not_lt_zero _ hb)
    · exact hx j (HistorySymbolicScope.above_atoms e he (Sum.inr j) hj)
  exact ⟨hsafe.1.fieldRegular x hf (hunit _ ha.1 hfree.1),
    hsafe.2.fieldRegular x hf (hunit _ ha.2 hfree.2)⟩

end Ostmann.Arithmetic.HistoryFieldIndependence

end

end OAI
