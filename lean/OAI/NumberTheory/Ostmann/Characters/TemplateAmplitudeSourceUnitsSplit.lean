import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem sampleUnitMultiplier_scheduledSample (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    sampleUnitMultiplier (schedule k j) width ζ (scheduledSample k j hj width w h y)=
      pivotUnitMultiplier k j hj width ζ w*survivorUnitMultiplier (schedule k j) j width ζ h y := by
  unfold sampleUnitMultiplier
  rw [← (scheduledConstituentInput k j hj width).prod_comp]
  simp only [scheduledSample,assemblePriorSample,Equiv.symm_apply_apply,Fintype.prod_sum_type,
    Sum.elim_inl,Sum.elim_inr]
  rfl

theorem sampleUnitMultiplier_nextSample (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData T width Q)
    (hL hR : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) :
    sampleUnitMultiplier (T.step j) width (nextUnitData T j width ζ) (nextSample T j width hL hR y)=
      (∏ i,ζ (copiedConstituentOld T j width i) (hL i))*
        conj (∏ i,ζ (copiedConstituentOld T j width i) (hR i)) := by
  unfold sampleUnitMultiplier
  rw [← (nextSampleEquiv T j width).prod_comp]
  simp only [nextSample,assemblePriorSample,Equiv.symm_apply_apply,Fintype.prod_sum_type,
    Sum.elim_inl,Sum.elim_inr]
  simp [nextUnitData,nextSampleEquiv,copyPairInputEquiv,map_prod]

end Ostmann.Characters.Template

end

end OAI
