import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesPrior
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceStates

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def constituentPrimePrior (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)) :
    FinitePrior (T.Constituent width → PrimeUpTo Q) :=
  productPrior (fun i => primeShellPrior (E i) (hE i))

def copiedPrimePrior (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)) :
    FinitePrior (CopiedConstituent T j width → PrimeUpTo Q) :=
  productPrior (fun i => primeShellPrior (E (copiedConstituentOld T j width i))
    (hE (copiedConstituentOld T j width i)))

def outsidePrimePrior (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)) :
    FinitePrior (OutsideConstituent T j width → PrimeUpTo Q) :=
  productPrior (fun i => primeShellPrior (E (outsideConstituentOld T j width i))
    (hE (outsideConstituentOld T j width i)))

def pivotPrimePrior (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) :
    FinitePrior (Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q) :=
  characterTuplePrior (fun a => E ⟨(pivotSlot k j hj).val,a⟩)
    (fun a => hE ⟨(pivotSlot k j hj).val,a⟩)

def constituentSampleState (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) : T.Slot → ℤ :=
  fun i => ∏ a : Fin (width (T.role i)), ((x ⟨i,a⟩).val:ℤ)

def copiedSampleState (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (x : CopiedConstituent T j width → PrimeUpTo Q) :
    {i:T.Slot // T.IsCopied j i} → ℤ :=
  fun i => ∏ a : Fin (width (T.role i.val)), ((x ⟨i,a⟩).val:ℤ)

def outsideSampleState (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (x : OutsideConstituent T j width → PrimeUpTo Q) :
    {i:T.Slot // T.IsOutside j i} → ℤ :=
  fun i => ∏ a : Fin (width (T.role i.val)), ((x ⟨i,a⟩).val:ℤ)

def scheduledSample (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    (schedule k j).Constituent width → PrimeUpTo Q :=
  assemblePriorSample (scheduledConstituentInput k j hj width) w h y

def copyPairInputEquiv (H Y : Type*) : H ⊕ (H ⊕ Y) ≃ (H × Bool) ⊕ Y where
  toFun
    | .inl h => .inl (h,true)
    | .inr (.inl h) => .inl (h,false)
    | .inr (.inr y) => .inr y
  invFun
    | .inl (h,b) => if b then .inl h else .inr (.inl h)
    | .inr y => .inr (.inr y)
  left_inv x := by rcases x with h | (h | y) <;> rfl
  right_inv x := by rcases x with ⟨h,_ | _⟩ | y <;> rfl

def nextSampleEquiv (T : Layout) (j : ℕ) (width : Role → ℕ) :
    CopiedConstituent T j width ⊕ (CopiedConstituent T j width ⊕ OutsideConstituent T j width) ≃
      (T.step j).Constituent width :=
  (copyPairInputEquiv _ _).trans (nextConstituentEquiv T j width).symm

def nextPrimeShells (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) :
    (T.step j).Constituent width → Finset (PrimeUpTo Q) := fun i =>
  match nextConstituentEquiv T j width i with
  | .inl (h,_) => E (copiedConstituentOld T j width h)
  | .inr y => E (outsideConstituentOld T j width y)

theorem nextPrimeShells_positive (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)) :
    ∀ i, 0 < primeShellMass (nextPrimeShells T j width E i) := by
  intro i
  unfold nextPrimeShells
  split <;> exact hE _

def nextSample (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (hL hR : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) : (T.step j).Constituent width → PrimeUpTo Q :=
  assemblePriorSample (nextSampleEquiv T j width) hL hR y

end Ostmann.Characters.Template

end

end OAI
