import OAI.NumberTheory.Ostmann.Characters.TemplateGraphFibers

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateDiagonalMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev CodePerm {I C : Type*} (code : I → C) :=
  {e : Equiv.Perm I // ∀i,code (e i)=code i}

theorem codePerm_card_le_product {I C : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (code : I → C) :
    Fintype.card (CodePerm code) ≤ ∏i,Fintype.card {j : I // code j=code i} := by
  classical
  let f : CodePerm code → (∀i,{j : I // code j=code i}) :=
    fun e i => ⟨e.val i,e.property i⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact congrArg Subtype.val (congrFun h i)
  exact (Fintype.card_le_of_injective f hf).trans_eq Fintype.card_pi

theorem codePerm_card_le {I C : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (code : I → C) (B : ℕ)
    (hB : ∀i,Fintype.card {j : I // code j=code i}≤B) :
    Fintype.card (CodePerm code)≤B^(Fintype.card I) := by
  refine (codePerm_card_le_product code).trans ?_
  calc
    _ ≤ ∏_i : I,B := Finset.prod_le_prod (fun i _ => hB i)
    _ = _ := by simp

def bulkCode (k l m : ℕ) (x : Template.Word k l × Fin m) : Fin l → ℤˣ×ℤˣ :=
  AnchorCodes.code (fun _ => 1) (Template.pathSigns k l x.1)

def bulkCodeFiberEquiv (k l m : ℕ) (c : Fin l → ℤˣ×ℤˣ) :
    {x : Template.Word k l × Fin m // bulkCode k l m x=c} ≃
      ({w : Template.Word k l // AnchorCodes.code (fun _ => 1) (Template.pathSigns k l w)=c} × Fin m) where
  toFun x := (⟨x.val.1,x.property⟩,x.val.2)
  invFun x := ⟨(x.1.val,x.2),x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bulkCode_fiber_card_le (k l m : ℕ) (c : Fin l → ℤˣ×ℤˣ) :
    Fintype.card {x : Template.Word k l × Fin m // bulkCode k l m x=c}≤2*m := by
  rw [Fintype.card_congr (bulkCodeFiberEquiv k l m c)]
  exact Template.actual_code_slots_le k l m c

theorem bulkCodePerm_card_le (k l m : ℕ) :
    Fintype.card (CodePerm (bulkCode k l m))≤(2*m)^(2^l*m) := by
  have h := codePerm_card_le (bulkCode k l m) (2*m)
    (fun i => bulkCode_fiber_card_le k l m (bulkCode k l m i))
  simpa only [Fintype.card_prod,Fintype.card_fin,Template.active_word_card] using h

end Ostmann.Characters.TemplateDiagonalMatching

end

end OAI
