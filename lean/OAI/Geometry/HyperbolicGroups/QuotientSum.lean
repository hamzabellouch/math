import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv
attribute [local instance] Classical.propDecidable
variable {D A : Type*}

/-- Exact class decomposition under an invariant predicate. -/
def quotientSplitEquiv (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) :
    Quotient (s.comap (Subtype.val : Subtype P → D)) ⊕
      Quotient (s.comap (Subtype.val : {x : D // ¬ P x} → D)) ≃ Quotient s := by
  classical
  let qP : Quotient s → Prop := Quotient.lift P (fun _ _ h => propext (hP h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype P (s₁ := s)
    (s₂ := s.comap Subtype.val) qP (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun x => ¬ P x) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun q => ¬ qP q) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  exact (e₁.symm.sumCongr e₂.symm).trans (Equiv.sumCompl qP)

@[simp] lemma quotientSplitEquiv_inl (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) (x : Subtype P) :
    quotientSplitEquiv s P hP (Sum.inl (Quotient.mk _ x)) = Quotient.mk s x.val := rfl

@[simp] lemma quotientSplitEquiv_inr (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) (x : {x : D // ¬ P x}) :
    quotientSplitEquiv s P hP (Sum.inr (Quotient.mk _ x)) = Quotient.mk s x.val := rfl

variable [Fintype D] [AddCommMonoid A]

/-- Sum of a weight ONCE per actual equivalence class. -/
def classSum (s : Setoid D) (w : D → A) (hw : s ≤ Setoid.ker w) : A := by
  classical
  exact ∑ q : Quotient s, Quotient.lift w (fun _ _ h => hw h) q

/-- Restriction partitions the exact sum of class weights. -/
theorem classSum_split (s : Setoid D) (w : D → A) (hw : s ≤ Setoid.ker w)
    (P : D → Prop) (hP : ∀ {x y}, s x y → (P x ↔ P y)) :
    classSum s w hw =
      classSum (s.comap (Subtype.val : Subtype P → D)) (w ∘ Subtype.val) (fun _ _ h => hw h) +
      classSum (s.comap (Subtype.val : {x : D // ¬ P x} → D)) (w ∘ Subtype.val) (fun _ _ h => hw h) := by
  classical
  let e := quotientSplitEquiv s P hP
  let v : Quotient s → A := Quotient.lift w (fun _ _ h => hw h)
  let v₁ : Quotient (s.comap (Subtype.val : Subtype P → D)) → A :=
    Quotient.lift (w ∘ Subtype.val) (fun _ _ h => hw h)
  let v₂ : Quotient (s.comap (Subtype.val : {x : D // ¬ P x} → D)) → A :=
    Quotient.lift (w ∘ Subtype.val) (fun _ _ h => hw h)
  have he : ∀ x, Sum.elim v₁ v₂ x = v (e x) := by
    intro x
    cases x with
    | inl x => induction x using Quotient.inductionOn; rfl
    | inr x => induction x using Quotient.inductionOn; rfl
  have hh := Fintype.sum_equiv e (Sum.elim v₁ v₂) v he
  rw [Fintype.sum_sum_type] at hh
  exact hh.symm

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
