import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsNorms
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsSplit

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem survivorUnitMultiplier_pair (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q) (hζ : ∀ i p,‖ζ i p‖=1)
    (hL hR : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) :
    survivorUnitMultiplier T j width ζ hL y*conj (survivorUnitMultiplier T j width ζ hR y)=
      sampleUnitMultiplier (T.step j) width (nextUnitData T j width ζ) (nextSample T j width hL hR y) := by
  have hn : ‖∏ i,ζ (outsideConstituentOld T j width i) (y i)‖=1 := by
    simp [norm_prod,hζ]
  have hc : (∏ i,ζ (outsideConstituentOld T j width i) (y i))*
      conj (∏ i,ζ (outsideConstituentOld T j width i) (y i))=1 := by
    rw [Complex.mul_conj',hn]
    norm_num
  rw [sampleUnitMultiplier_nextSample]
  unfold survivorUnitMultiplier
  rw [map_mul]
  calc
    _ = ((∏ i,ζ (copiedConstituentOld T j width i) (hL i))*
        conj (∏ i,ζ (copiedConstituentOld T j width i) (hR i)))*
        ((∏ i,ζ (outsideConstituentOld T j width i) (y i))*
          conj (∏ i,ζ (outsideConstituentOld T j width i) (y i))) := by ring
    _ = _ := by rw [hc,mul_one]

@[simp] theorem sampleUnitMultiplier_scheduled_zero (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ0 : PrimeUnitData (schedule k 0) width Q)
    (x : (schedule k 0).Constituent width → PrimeUpTo Q) :
    sampleUnitMultiplier (schedule k 0) width (scheduledUnitData k width ζ0 0) x =
      ∏ i,ζ0 i (x i) := rfl

theorem scheduled_survivorUnitMultiplier_pair (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ0 : PrimeUnitData (schedule k 0) width Q) (hζ0 : ∀ i p,‖ζ0 i p‖=1)
    (hL hR : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    survivorUnitMultiplier (schedule k j) j width (scheduledUnitData k width ζ0 j) hL y*
      conj (survivorUnitMultiplier (schedule k j) j width (scheduledUnitData k width ζ0 j) hR y)=
    sampleUnitMultiplier (schedule k (j+1)) width (scheduledUnitData k width ζ0 (j+1))
      (nextSample (schedule k j) j width hL hR y) :=
  survivorUnitMultiplier_pair _ _ _ _ (norm_scheduledUnitData k width ζ0 hζ0 j) _ _ _

end Ostmann.Characters.Template

end

end OAI
