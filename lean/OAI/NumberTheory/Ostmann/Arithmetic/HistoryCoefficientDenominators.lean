import OAI.NumberTheory.Ostmann.Arithmetic.HistoryNumeratorForms
import OAI.NumberTheory.Ostmann.Arithmetic.SafeRationalExpressions

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCoefficientDenominators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistorySymbolicSlots
open HistorySymbolicScope HistoryNumeratorForms SafeRationalExpressions

variable {ι : Type*}

def StateSafe (S : Set ℤ) {a : State} (e : StateExpr a ι) : Prop :=
  Expression S e.plus ∧ Expression S e.minus ∧ ∀ i, Denominator S (e.small i)

theorem append_denominator {S : Set ℤ} {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : ∀ i, Denominator S (f i)) (hg : ∀ i, Denominator S (g i)) :
    ∀ i, Denominator S (append f g i) := by
  intro i
  change Denominator S (Fin.append f g _)
  refine Fin.addCases (motive := fun j : Fin (xs.length+ys.length) =>
    Denominator S (Fin.append f g j)) ?_ ?_ _
  · intro j
    simpa only [Fin.append_left] using hf j
  · intro j
    simpa only [Fin.append_right] using hg j

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem nodeNumerator_safe {S : Set ℤ}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (he : StateSafe S e) : Expression S (nodeNumerator hs e) := by
  have hP : Denominator S (HistorySymbolicStep.product
      (List.ofFn (leftPart (splitSlots hs e)))) :=
    Denominator.product_ofFn _ (fun _ => he.2.2 _)
  have hM : Denominator S (HistorySymbolicStep.product
      (List.ofFn (rightPart (splitSlots hs e)))) :=
    Denominator.product_ofFn _ (fun _ => he.2.2 _)
  exact .sub (.mul (.fixed _) (.mul he.2.1 hM.expression))
    (.mul (.fixed _) (.mul he.1 hP.expression))

theorem child_safe {S : Set ℤ}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (he : StateSafe S e) (hc : ∀ i, Denominator S (comp i))
    (hf : a.frequency ∈ S) :
    StateSafe S (leftState hs e comp) ∧ StateSafe S (rightState hs e comp) := by
  have hN := nodeNumerator_safe hs e he
  have hU := Denominator.product_ofFn comp hc
  have hPivot : Expression S (pivotExpr hs e comp) :=
    .divide hN (.mul (.frequency _ hf) hU)
  have hleft : ∀ i, Denominator S (leftPart (splitSlots hs e) i) := fun _ => he.2.2 _
  have hright : ∀ i, Denominator S (rightPart (splitSlots hs e) i) := fun _ => he.2.2 _
  exact ⟨⟨hPivot,he.1,fun _ => append_denominator comp _ hc hleft _⟩,
    ⟨hPivot,he.2.1,fun _ => append_denominator comp _ hc hright _⟩⟩

def TreeSafe (S : Set ℤ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateSafe S e
  | _, .node _ _ _ _ _ left right, e =>
      StateSafe S e.1 ∧ TreeSafe S left e.2.1 ∧ TreeSafe S right e.2.2

theorem encode_safe {S : Set ℤ} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (he : StateSafe S e)
    (hc : ∀ i, Denominator S (comp i)) (hf : ∀ s ∈ h.frequencies, s ∈ S) :
    TreeSafe S h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
      have hchildren := child_safe hs e (fun i => comp (Sum.inl i)) he
        (fun i => hc (Sum.inl i)) (hf _ (by simp [History.frequencies]))
      refine ⟨he,?_,?_⟩
      · exact ihl (History.supported_left hs) _ _ hchildren.1
          (fun i => hc (Sum.inr (Sum.inl i)))
          (fun s hmem => hf s (by simp [History.frequencies,hmem]))
      · exact ihr (History.supported_right hs) _ _ hchildren.2
          (fun i => hc (Sum.inr (Sum.inr i)))
          (fun s hmem => hf s (by simp [History.frequencies,hmem]))

theorem symbolicHistory_safe {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeSafe {s | s ∈ h.frequencies} h (symbolicHistory h hs) := by
  apply encode_safe
  · exact ⟨.atom _,.atom _,fun _ => .atom _⟩
  · exact fun _ => .atom _
  · exact fun _ hmem => hmem

theorem coefficientHistory_safe {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeSafe {s | s ∈ h.frequencies} h (coefficientHistory h hs second) := by
  apply encode_safe
  · exact ⟨.fixed _,.fixed _,fun _ => .atom _⟩
  · exact fun _ => .atom _
  · exact fun _ hmem => hmem

theorem nodeNumerator_field_regular {S : Set ℤ} {K : Type*} [Field K] [DecidableEq ι]
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (he : StateSafe S e) (level : ι → ℕ)
    (ha : StateAbove level (l+1) e) (x : ι → K)
    (hS : ∀ s ∈ S, (s:K) ≠ 0) (hx : ∀ i, l+1 < level i → x i ≠ 0) :
    (nodeNumerator hs e).FieldRegularAt x :=
  (nodeNumerator_safe hs e he).fieldRegular x hS
    (fun i hi => hx i (above_atoms _ (nodeNumerator_above hs e level ha) i hi))

theorem nodeNumerator_denominator_nonzero {S : Set ℤ} {K : Type*}
    [Field K] [DecidableEq ι]
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (he : StateSafe S e) (level : ι → ℕ)
    (ha : StateAbove level (l+1) e) (x : ι → K)
    (hS : ∀ s ∈ S, (s:K) ≠ 0) (hx : ∀ i, l+1 < level i → x i ≠ 0) :
    MvPolynomial.eval₂ (Int.castRingHom K) x (nodeNumerator hs e).denominator ≠ 0 :=
  ((nodeNumerator hs e).field_cleared x
    (nodeNumerator_field_regular hs e he level ha x hS hx)).1

end Ostmann.Arithmetic.HistoryCoefficientDenominators

end

end OAI
