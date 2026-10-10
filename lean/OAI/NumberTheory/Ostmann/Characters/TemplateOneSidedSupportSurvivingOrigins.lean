import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressionsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SurvivingSlot (k j : ℕ) :=
  {i:(schedule k j).Slot // (schedule k j).IsCopied j i} ⊕
  {i:(schedule k j).Slot // (schedule k j).IsOutside j i}

def survivingWidth (k j : ℕ) (width : Role→ℕ) : SurvivingSlot k j→ℕ
  | .inl i => width ((schedule k j).role i.val)
  | .inr i => width ((schedule k j).role i.val)

def survivingPrimeEquiv (k j : ℕ) (width : Role→ℕ) :
    (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i)) ≃ SurvivingPrimeIndex k j width where
  toFun
    | ⟨.inl i,a⟩ => .inl ⟨i,a⟩
    | ⟨.inr i,a⟩ => .inr ⟨i,a⟩
  invFun
    | .inl ⟨i,a⟩ => ⟨.inl i,a⟩
    | .inr ⟨i,a⟩ => ⟨.inr i,a⟩
  left_inv := by rintro ⟨i,a⟩; cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

def pairedOrigins (k j : ℕ) : SampleOrigins k (j+1) (SurvivingSlot k j) where
  origin
    | .inl (i,_) => some (.inl i)
    | .inr i => some (.inr i)
  missing := by intro i h; cases i <;> cases h

def origins (k j : ℕ) : SampleOrigins k j (SurvivingSlot k j) :=
  (pairedOrigins k j).child true

@[simp] theorem origins_pivot (k j : ℕ) (i : (schedule k j).Slot)
    (hi : (schedule k j).IsPivot j i) : (origins k j).origin i=none := by
  simp only [origins,SampleOrigins.child,dite_eq_left hi]

@[simp] theorem origins_copied (k j : ℕ)
    (i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}) :
    (origins k j).origin i.val=some (.inl i) := by
  have hp : ¬(schedule k j).IsPivot j i.val := fun h=>pivot_not_copied _ _ _ h i.property
  simp only [origins,SampleOrigins.child,dite_eq_right hp,dite_eq_left i.property,pairedOrigins]

@[simp] theorem origins_outside (k j : ℕ)
    (i : {i:(schedule k j).Slot // (schedule k j).IsOutside j i}) :
    (origins k j).origin i.val=some (.inr i) := by
  simp only [origins,SampleOrigins.child,dite_eq_right i.property.1,
    dite_eq_right i.property.2,pairedOrigins]

theorem origins_matches (k j : ℕ) (P : ℤ) (h : CopiedState k j) (y : OutsideState k j) :
    (origins k j).Matches (Sum.elim h y) (sourceState k j P h y) := by
  have hp : (pairedOrigins k j).Matches (Sum.elim h y) (pairedState k j h h y) := by
    intro i a ha
    cases i with
    | inl z =>
      change some (.inl z.1)=some a at ha
      cases Option.some.inj ha
      rcases z with ⟨i,b⟩
      cases b <;> rfl
    | inr i =>
      change some (.inr i)=some a at ha
      cases Option.some.inj ha
      rfl
  exact hp.child true P

theorem origins_matches_products (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (x : (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ) :
    (origins k j).Matches (fun i=>∏a,x ⟨i,a⟩)
      (sourceState k j P (fun i=>∏a,x ⟨.inl i,a⟩) (fun i=>∏a,x ⟨.inr i,a⟩)) := by
  convert origins_matches k j P (fun i=>∏a,x ⟨.inl i,a⟩) (fun i=>∏a,x ⟨.inr i,a⟩) using 1
  funext i
  cases i <;> rfl

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
