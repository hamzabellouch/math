import OAI.NumberTheory.Ostmann.Characters.TemplateAdaptedCoordinates
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Preliminaries
attribute [local instance] Classical.propDecidable

def IsChosen (k j:ℕ) (width:Role→ℕ) (i:(schedule k j).Constituent width) : Prop :=
  (schedule k j).eligible i.1 ∧ (schedule k j).role i.1=.word ∧ i.2.val=0

abbrev RemainingPrime (k j:ℕ) (width:Role→ℕ) :=
  {i:(schedule k j).Constituent width // ¬IsChosen k j width i}

def chosenPrimeIndex (k j:ℕ) (width:Role→ℕ) (hw:0<width .word) (w:WordSlot k j) :
    (schedule k j).Constituent width :=
  ⟨w.val,⟨0,by simpa only [w.property.2] using hw⟩⟩

theorem chosenPrimeIndex_chosen (k j:ℕ) (width:Role→ℕ) (hw:0<width .word)
    (w:WordSlot k j) : IsChosen k j width (chosenPrimeIndex k j width hw w) :=
  ⟨w.property.1,w.property.2,rfl⟩

def chosenPrimeSplit (k j:ℕ) (width:Role→ℕ) (hw:0<width .word) :
    WordSlot k j ⊕ RemainingPrime k j width ≃ (schedule k j).Constituent width where
  toFun
    | .inl w => chosenPrimeIndex k j width hw w
    | .inr i => i.val
  invFun i := if h:IsChosen k j width i then .inl ⟨i.1,h.1,h.2.1⟩ else .inr ⟨i,h⟩
  left_inv w := by
    cases w with
    | inl w => simp only [chosenPrimeIndex_chosen,dite_eq_left]; rfl
    | inr i => simp only [dite_eq_right i.property]
  right_inv i := by
    dsimp only
    split_ifs with h
    · change chosenPrimeIndex k j width hw ⟨i.1,h.1,h.2.1⟩ = i
      rcases i with ⟨i,a⟩
      unfold chosenPrimeIndex
      congr 1
      apply Fin.ext
      exact h.2.2.symm
    · rfl

def assembleChosen {Q:ℕ} (k j:ℕ) (width:Role→ℕ)
    (y:RemainingPrime k j width→PrimeUpTo Q) (z:WordSlot k j→PrimeUpTo Q) :
    (schedule k j).Constituent width→PrimeUpTo Q := fun i=>
  if h:IsChosen k j width i then z ⟨i.1,h.1,h.2.1⟩ else y ⟨i,h⟩

def chosenContext {Q:ℕ} (k j:ℕ) (width:Role→ℕ)
    (y:RemainingPrime k j width→PrimeUpTo Q) : State k j := fun i=>
  ∏a:Fin (width ((schedule k j).role i)),
    if h:IsChosen k j width ⟨i,a⟩ then 1 else ((y ⟨⟨i,a⟩,h⟩).val:ℤ)

theorem constituentSampleState_assembleChosen {Q:ℕ} (k j:ℕ) (width:Role→ℕ)
    (hw:0<width .word) (y:RemainingPrime k j width→PrimeUpTo Q)
    (z:WordSlot k j→PrimeUpTo Q) :
    constituentSampleState (schedule k j) width (assembleChosen k j width y z)=
      installWords k j (chosenContext k j width y) (fun w=>(z w).val:WordSlot k j→ℤ) := by
  funext i
  change (∏a:Fin (width ((schedule k j).role i)),
    ((assembleChosen k j width y z ⟨i,a⟩).val:ℤ))=_
  have hp (a:Fin (width ((schedule k j).role i))) :
      ((assembleChosen k j width y z ⟨i,a⟩).val:ℤ)=
        (if h:IsChosen k j width ⟨i,a⟩ then 1 else ((y ⟨⟨i,a⟩,h⟩).val:ℤ))*
        (if h:IsChosen k j width ⟨i,a⟩ then ((z ⟨i,h.1,h.2.1⟩).val:ℤ) else 1) := by
    unfold assembleChosen
    split_ifs <;> simp only [one_mul,mul_one]
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  change chosenContext k j width y i * _=chosenContext k j width y i * _
  congr 1
  by_cases hi:(schedule k j).eligible i ∧ (schedule k j).role i=.word
  · let a0 : Fin (width ((schedule k j).role i)) := ⟨0,by simpa only [hi.2] using hw⟩
    have hc : IsChosen k j width ⟨i,a0⟩ := ⟨hi.1,hi.2,rfl⟩
    rw [dite_eq_left hi,Finset.prod_eq_single a0]
    · exact dite_eq_left hc
    · intro a ha hne
      apply dite_eq_right
      intro h
      exact hne (Fin.ext h.2.2)
    · simp
  · rw [dite_eq_right hi]
    apply Finset.prod_eq_one
    intro a ha
    apply dite_eq_right
    intro h
    exact hi ⟨h.1,h.2.1⟩

end Ostmann.Characters.Template

end

end OAI
