import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatchingCount

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateDiagonalMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def wholeCode (k l m : ℕ) (J : Type*) : (Template.Word k l × Fin m) ⊕ J →
    (Fin l → ℤˣ×ℤˣ) ⊕ Unit :=
  Sum.elim (fun x => Sum.inl (bulkCode k l m x)) (fun _ => Sum.inr ())

def wholeCodeBulkFiberEquiv (k l m : ℕ) (J : Type*)
    (c : Fin l → ℤˣ×ℤˣ) :
    {x : (Template.Word k l × Fin m) ⊕ J // wholeCode k l m J x=Sum.inl c} ≃
      {x : Template.Word k l × Fin m // bulkCode k l m x=c} where
  toFun x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl x => exact ⟨x,Sum.inl.inj hx⟩
    | inr j => cases hx
  invFun x := ⟨Sum.inl x.val,congrArg Sum.inl x.property⟩
  left_inv x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl x => rfl
    | inr j => cases hx
  right_inv x := rfl

def wholeCodeNonbulkFiberEquiv (k l m : ℕ) (J : Type*) :
    {x : (Template.Word k l × Fin m) ⊕ J // wholeCode k l m J x=Sum.inr ()} ≃ J where
  toFun x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl x => cases hx
    | inr j => exact j
  invFun j := ⟨Sum.inr j,rfl⟩
  left_inv x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl x => cases hx
    | inr j => rfl
  right_inv _ := rfl

instance wholeCodePermFintype (k l m : ℕ) (J : Type*) [Fintype J] [DecidableEq J] :
    Fintype (CodePerm (wholeCode k l m J)) := Subtype.fintype _

theorem wholeCodePerm_card_le (k l m : ℕ) (J : Type*) [Fintype J] [DecidableEq J] :
    Fintype.card (CodePerm (wholeCode k l m J))≤
      (2*m)^(2^l*m)*(Fintype.card J)^(Fintype.card J) := by
  apply (codePerm_card_le_product (wholeCode k l m J)).trans
  rw [Fintype.prod_sum_type]
  have hbulk : (∏x : Template.Word k l × Fin m,
      Fintype.card {y // wholeCode k l m J y=wholeCode k l m J (Sum.inl x)})≤(2*m)^(2^l*m) := by
    calc
      _ ≤ ∏_x : Template.Word k l × Fin m,2*m := by
        apply Finset.prod_le_prod
        intro x hx
        change Fintype.card {y // wholeCode k l m J y=Sum.inl (bulkCode k l m x)}≤2*m
        rw [Fintype.card_congr (wholeCodeBulkFiberEquiv k l m J (bulkCode k l m x))]
        exact bulkCode_fiber_card_le k l m _
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,
        Fintype.card_fin,Template.active_word_card]
  have hother : (∏x : J,
      Fintype.card {y // wholeCode k l m J y=wholeCode k l m J (Sum.inr x)})=
      (Fintype.card J)^(Fintype.card J) := by
    have hh (x : J) : Fintype.card {y // wholeCode k l m J y=wholeCode k l m J (Sum.inr x)}=
        Fintype.card J := Fintype.card_congr (wholeCodeNonbulkFiberEquiv k l m J)
    simp only [hh,Finset.prod_const,Finset.card_univ]
  rw [hother]
  exact Nat.mul_le_mul_right _ hbulk

end Ostmann.Characters.TemplateDiagonalMatching

end

end OAI
