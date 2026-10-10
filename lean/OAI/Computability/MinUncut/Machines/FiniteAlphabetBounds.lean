import Mathlib
import OAI.Computability.MinUncut.Search.FiniteQueryFamily

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

lemma secondSlot_card_le (q : SecondQuestion Name) : Fintype.card (secondSlot q)≤8 := by
  cases q <;> norm_num [secondSlot,secondSlotCount,Fintype.card_fun,F₂,ZMod.card]

lemma secondAlphabet_card_le (Q : I → SecondQuestion Name) :
    Fintype.card (SecondAlphabet Q)≤2^(3*Fintype.card I) := by
  calc
    Fintype.card (SecondAlphabet Q)=∏ i, Fintype.card (secondSlot (Q i)) := Fintype.card_pi
    _ ≤ ∏ _i : I, 8 := Finset.prod_le_prod (fun i _ => secondSlot_card_le (Q i))
    _ = 2^(3*Fintype.card I) := by rw [Finset.prod_const,Finset.card_univ,pow_mul]; norm_num

lemma alphabet_card_le (E : Equation Name) : Fintype.card (alphabet E)≤8 := by
  have hh := Fintype.card_le_of_injective (fun a : alphabet E => (a:Triple)) Subtype.val_injective
  convert hh using 1; norm_num [Triple,Fintype.card_fun,F₂,ZMod.card]

lemma firstAlphabet_card_le (U : I → Equation Name) :
    Fintype.card (FirstAlphabet U)≤2^(3*Fintype.card I) := by
  calc
    Fintype.card (FirstAlphabet U)=∏ i, Fintype.card (alphabet (U i)) := Fintype.card_pi
    _ ≤ ∏ _i : I, 8 := Finset.prod_le_prod (fun i _ => alphabet_card_le (U i))
    _ = 2^(3*Fintype.card I) := by rw [Finset.prod_const,Finset.card_univ,pow_mul]; norm_num

lemma familyAlphabet_card_le (q : FamilyQuestion Name I) :
    Fintype.card (FamilyAlphabet q)≤2^(3*Fintype.card I) := by
  cases q with
  | inl U => exact firstAlphabet_card_le U
  | inr Q => exact secondAlphabet_card_le Q

lemma forms_card_le {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] :
    Fintype.card (Forms A)≤2^Fintype.card A := by
  have hh := Fintype.card_le_of_injective (fun f : Forms A => (f : A → F₂)) AffineMap.coeFn_injective
  simpa only [Fintype.card_fun,F₂,ZMod.card] using hh

def faceCardBound (t m n : ℕ) := (2^(2^(3*t)))^Fintype.card (Row m n)

lemma faceArray_card_le (Q : I → SecondQuestion Name) (m n : ℕ) :
    Fintype.card (FaceArray (SecondAlphabet Q) m n)≤faceCardBound (Fintype.card I) m n := by
  simp only [FaceArray,Fintype.card_fun,faceCardBound]
  exact Nat.pow_le_pow_left ((forms_card_le).trans (Nat.pow_le_pow_right (by omega) (secondAlphabet_card_le Q))) _

variable [Fintype Name]
lemma equation_card : Fintype.card (Equation Name)=2*Fintype.card Name^3 := by
  let e : Equation Name ≃ ((Fin 3 → Name) × F₂) :=
    ⟨fun E => (E.names,E.rhs),fun p => ⟨p.1,p.2⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  simp only [F₂,ZMod.card,mul_comm]

lemma familyQuestion_card : Fintype.card (FamilyQuestion Name I)=
    (2*Fintype.card Name^3)^Fintype.card I+
      (Fintype.card Name+2*Fintype.card Name^3)^Fintype.card I := by
  simp only [FamilyQuestion,Fintype.card_sum,Fintype.card_fun,SecondQuestion,equation_card]

lemma familyVariable_card_le : Fintype.card (FamilyVariable Name I)≤
    Fintype.card (FamilyQuestion Name I)*2^(2^(3*Fintype.card I)) := by
  calc
    Fintype.card (FamilyVariable Name I)=
      ∑ q : FamilyQuestion Name I, Fintype.card {R : FamilyAlphabet q → Bool // R (familyBase q)=true} :=
        Fintype.card_sigma
    _ ≤ ∑ q : FamilyQuestion Name I, 2^(2^(3*Fintype.card I)) := by
      apply Finset.sum_le_sum
      intro q _
      have hh := Fintype.card_le_of_injective
        (fun R : {R : FamilyAlphabet q → Bool // R (familyBase q)=true} => R.val) Subtype.val_injective
      have hh' : Fintype.card {R : FamilyAlphabet q → Bool // R (familyBase q)=true}≤
          2^Fintype.card (FamilyAlphabet q) := by simpa only [Fintype.card_fun,Fintype.card_bool] using hh
      exact hh'.trans (Nat.pow_le_pow_right (by omega) (familyAlphabet_card_le q))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
end MinUncut.Outer

end
end

end OAI
