import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSampleUnits
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingOrigins

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template Preliminaries
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sourceState_pairwise_of_surviving {k j : ℕ} (hj : j<k) (P : ℤ)
    (h : CopiedState k j) (y : OutsideState k j)
    (hpairs : Pairwise (fun i v : SurvivingSlot k j=>IsCoprime (Sum.elim h y i) (Sum.elim h y v)))
    (hpivot : ∀i : SurvivingSlot k j,IsCoprime (Sum.elim h y i) P) :
    Pairwise (fun i v=>IsCoprime (sourceState k j P h y i) (sourceState k j P h y v)) := by
  let e := oldIndexEquiv (schedule k j) j (pivotSlot k j hj) (pivotSlot_unique k j hj)
  have he (a : Option (SurvivingSlot k j)) :
      sourceState k j P h y (e a) = match a with | none=>P | some i=>Sum.elim h y i := by
    cases a with
    | none =>
      exact childState_pivot k j true _ P _ (pivotSlot k j hj).property
    | some i =>
      cases i with
      | inl i => exact sourceState_copied_value P h y i
      | inr i => exact sourceState_outside_value P h y i
  intro i v hiv
  obtain ⟨a,rfl⟩ := e.surjective i
  obtain ⟨b,rfl⟩ := e.surjective v
  rw [he a,he b]
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hiv rfl)
    | some b => exact (hpivot b).symm
  | some a =>
    cases b with
    | none => exact hpivot a
    | some b => exact hpairs (fun hab=>hiv (congrArg e (congrArg some hab)))

theorem grouped_sourceState_pairwise {k j : ℕ} (hj : j<k) (width : Role→ℕ) (P : ℤ)
    (x : (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ)
    (hpairs : Pairwise (fun i v=>IsCoprime (x i) (x v)))
    (hpivot : ∀i,IsCoprime (x i) P) :
    Pairwise (fun i v=>IsCoprime
      (sourceState k j P (fun i=>∏a,x ⟨.inl i,a⟩) (fun i=>∏a,x ⟨.inr i,a⟩) i)
      (sourceState k j P (fun i=>∏a,x ⟨.inl i,a⟩) (fun i=>∏a,x ⟨.inr i,a⟩) v)) := by
  have he (i : SurvivingSlot k j) :
      Sum.elim (fun i=>∏a,x ⟨.inl i,a⟩) (fun i=>∏a,x ⟨.inr i,a⟩) i = ∏a,x ⟨i,a⟩ := by
    cases i <;> rfl
  apply sourceState_pairwise_of_surviving hj P _ _
  · intro i v hiv
    rw [he i,he v]
    apply IsCoprime.prod_left
    intro a ha
    apply IsCoprime.prod_right
    intro b hb
    exact hpairs (fun hh=>hiv (congrArg Sigma.fst hh))
  · intro i
    rw [he i]
    exact IsCoprime.prod_left (fun a _=>hpivot ⟨i,a⟩)

theorem grouped_prime_sourceState {k j Q : ℕ} (width : Role→ℕ) (P : ℤ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) :
    sourceState k j P
      (fun i=>∏a,((p (survivingPrimeEquiv k j width ⟨.inl i,a⟩)).val:ℤ))
      (fun i=>∏a,((p (survivingPrimeEquiv k j width ⟨.inr i,a⟩)).val:ℤ)) =
    sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
      (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))) := rfl

theorem prime_sourceState_pairwise {k j Q : ℕ} (hj : j<k) (width : Role→ℕ) (P : ℕ+)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val))
    (hpivot : ∀i,(p i).val.Coprime P) :
    Pairwise (fun i v=>IsCoprime
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))) i)
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))) v)) := by
  apply grouped_sourceState_pairwise hj width (P:ℤ)
    (fun i=>((p (survivingPrimeEquiv k j width i)).val:ℤ))
  · intro i v hiv
    exact Nat.isCoprime_iff_coprime.mpr
      (hpairs (fun h=>hiv ((survivingPrimeEquiv k j width).injective h)))
  · intro i
    exact Nat.isCoprime_iff_coprime.mpr (hpivot _)

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
