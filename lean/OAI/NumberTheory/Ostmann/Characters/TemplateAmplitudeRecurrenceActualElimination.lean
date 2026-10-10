import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceEnergy
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSourceFactors
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSurvivorRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem retained_source_summand (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀i p,χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (scheduledSample k j hj width w h y i).val j s t) :
    (if samplePrimeSupport (schedule k j) width (scheduledSample k j hj width w h y) then
      retainedHistoryWeight k B V extra mask X Δ W j s
        (constituentSampleState (schedule k j) width (scheduledSample k j hj width w h y)) t *
      sampledHistoryPhase k j width χ a (scheduledSample k j hj width w h y) s t
    else 0) =
    if Pairwise (fun i i' => (w i).val.Coprime (w i').val) then
      sampledPivotOutgoing k j hj width χ a w y
        (historyRowTag k j (positiveTupleProduct w) (copiedSampleState (schedule k j) j width h) s)*
      RetainedRow.term k j B V extra mask X Δ W (positiveTupleProduct w)
        (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
        (s,t) (sampledRetainedPhase k j hj width χ a h y (positiveTupleProduct w) s t)
    else 0 := by
  let x := scheduledSample k j hj width w h y
  let wt := retainedHistoryWeight k B V extra mask X Δ W j s
    (constituentSampleState (schedule k j) width x) t
  have he : constituentSampleState (schedule k j) width x =
      sourceState k j (positiveTupleProduct w:ℤ)
        (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y) :=
    constituentSampleState_scheduledSample k j hj width w h y
  by_cases hw : wt=0
  · have hw' : retainedHistoryWeight k B V extra mask X Δ W j s
        (sourceState k j (positiveTupleProduct w:ℤ)
          (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)) t=0 :=
      he ▸ hw
    simp only [RetainedRow.term,hw',zero_mul,mul_zero,ite_self]
    change (if samplePrimeSupport (schedule k j) width x then wt*_ else 0)=0
    simp only [hw,zero_mul,ite_self]
  · have hc := (retainedHistoryWeight_support hw).current.pairwise
    have hiff : samplePrimeSupport (schedule k j) width x ↔
        Pairwise (fun i i' => (w i).val.Coprime (w i').val) ∧
        copiedWithinAtomPrimeSupport (schedule k j) j width h ∧
        outsideWithinAtomPrimeSupport (schedule k j) j width y := by
      rw [samplePrimeSupport_iff]
      simp only [hc,true_and]
      exact withinAtomPrimeSupport_scheduledSample k j hj width w h y
    by_cases hp : Pairwise (fun i i' => (w i).val.Coprime (w i').val)
    · rw [ite_eq_left hp]
      by_cases hs : copiedWithinAtomPrimeSupport (schedule k j) j width h ∧
          outsideWithinAtomPrimeSupport (schedule k j) j width y
      · have hglobal := hiff.mpr ⟨hp,hs⟩
        rw [ite_eq_left hglobal,sampledHistoryPhase_pivot_split k j hj width χ hχ a w h y s t hglobal ht]
        simp only [RetainedRow.term,sampledRetainedPhase,ite_eq_left hs]
        rw [he]
        ring
      · rw [ite_eq_right (fun hz => hs (hiff.mp hz).2)]
        simp only [RetainedRow.term,sampledRetainedPhase,ite_eq_right hs,mul_zero]
    · rw [ite_eq_right hp,ite_eq_right (fun hz => hp (hiff.mp hz).1)]

end Ostmann.Characters.Template

end

end OAI
