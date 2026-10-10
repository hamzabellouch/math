import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorSources

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

abbrev PrimeUnitData (T : Layout) (width : Role → ℕ) (Q : ℕ) :=
  T.Constituent width → PrimeUpTo Q → ℂ

def sampleUnitMultiplier (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q) (x : T.Constituent width → PrimeUpTo Q) : ℂ :=
  ∏ i,ζ i (x i)

def pivotUnitMultiplier (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q) : ℂ :=
  ∏ i,ζ ⟨(pivotSlot k j hj).val,i⟩ (w i)

def survivorUnitMultiplier (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q)
    (h : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) : ℂ :=
  (∏ i,ζ (copiedConstituentOld T j width i) (h i))*
    (∏ i,ζ (outsideConstituentOld T j width i) (y i))

def nextUnitData (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q) : PrimeUnitData (T.step j) width Q := fun i p =>
  match nextConstituentEquiv T j width i with
  | .inl (h,b) => if b then ζ (copiedConstituentOld T j width h) p
      else conj (ζ (copiedConstituentOld T j width h) p)
  | .inr _ => 1

def scheduledUnitData (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ0 : PrimeUnitData (schedule k 0) width Q) :
    (j : ℕ) → PrimeUnitData (schedule k j) width Q
  | 0 => ζ0
  | j+1 => nextUnitData (schedule k j) j width (scheduledUnitData k width ζ0 j)

@[simp] theorem scheduledUnitData_zero (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ0 : PrimeUnitData (schedule k 0) width Q) : scheduledUnitData k width ζ0 0=ζ0 := rfl

@[simp] theorem scheduledUnitData_succ (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ0 : PrimeUnitData (schedule k 0) width Q) :
    scheduledUnitData k width ζ0 (j+1)=
      nextUnitData (schedule k j) j width (scheduledUnitData k width ζ0 j) := rfl

end Ostmann.Characters.Template

end

end OAI
