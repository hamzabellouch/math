import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem norm_sampleUnitMultiplier (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q) (hζ : ∀ i p,‖ζ i p‖=1)
    (x : T.Constituent width → PrimeUpTo Q) : ‖sampleUnitMultiplier T width ζ x‖=1 := by
  simp [sampleUnitMultiplier,norm_prod,hζ]

theorem norm_pivotUnitMultiplier (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀ i p,‖ζ i p‖=1)
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q) :
    ‖pivotUnitMultiplier k j hj width ζ w‖=1 := by
  simp [pivotUnitMultiplier,norm_prod,hζ]

theorem norm_survivorUnitMultiplier (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q) (hζ : ∀ i p,‖ζ i p‖=1)
    (h : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) :
    ‖survivorUnitMultiplier T j width ζ h y‖=1 := by
  simp [survivorUnitMultiplier,norm_prod,hζ]

theorem norm_nextUnitData (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q) (hζ : ∀ i p,‖ζ i p‖=1) :
    ∀ i p,‖nextUnitData T j width ζ i p‖=1 := by
  intro i p
  rcases hh : nextConstituentEquiv T j width i with ⟨h,b⟩ | y
  · cases b <;> simp [nextUnitData,hh,hζ]
  · simp [nextUnitData,hh]

theorem norm_scheduledUnitData (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ0 : PrimeUnitData (schedule k 0) width Q) (hζ0 : ∀ i p,‖ζ0 i p‖=1) :
    ∀ j i p,‖scheduledUnitData k width ζ0 j i p‖=1 := by
  intro j
  induction j with
  | zero => exact hζ0
  | succ j ih => exact norm_nextUnitData _ _ _ _ ih

theorem norm_pivotUnitMultiplier_mul (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀ i p,‖ζ i p‖=1)
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q) (G : ℂ) :
    ‖pivotUnitMultiplier k j hj width ζ w*G‖=‖G‖ := by
  rw [norm_mul,norm_pivotUnitMultiplier k j hj width ζ hζ w,one_mul]

end Ostmann.Characters.Template

end

end OAI
