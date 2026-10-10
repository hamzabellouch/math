import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSourceFactorsSample
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitSource

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem retained_source_summand_of_sample (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (hχ : ∀i,χ i (scheduledSample k j hj width w h y i)≠1)
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
        rw [ite_eq_left hglobal,sampledHistoryPhase_pivot_split_of_sample k j hj width χ a w h y s t hχ hglobal ht]
        simp only [RetainedRow.term,sampledRetainedPhase,ite_eq_left hs]
        rw [he]
        ring
      · rw [ite_eq_right (fun hz => hs (hiff.mp hz).2)]
        simp only [RetainedRow.term,sampledRetainedPhase,ite_eq_right hs,mul_zero]
    · rw [ite_eq_right hp,ite_eq_right (fun hz => hp (hiff.mp hz).1)]

theorem norm_unitPivotOutgoing_le_of_sample (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀i p,‖ζ i p‖=1)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (u : ZMod (positiveTupleProduct w:ℕ))
    (hχ : ∀i,χ ⟨(pivotSlot k j hj).val,i⟩ (w i)≠1) :
    ‖unitPivotOutgoing k j hj width ζ χ a w y u‖≤1 := by
  rw [unitPivotOutgoing,norm_pivotUnitMultiplier_mul k j hj width ζ hζ]
  let : ∀i, Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
  exact norm_actualPivotOutgoing_le k j hj width _ _ hχ _ _ _

theorem unitAmplitudeIntegrand_source_of_sample (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hχ : ∀i,χ i (scheduledSample k j hj width w h y i)≠1)
    (ht : ∀z:SupportedHistory S j [],∀i,
      HistoryFrequencyUnits (scheduledSample k j hj width w h y i).val j z.val.1 z.val.2) :
    unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S
      (scheduledSample k j hj width w h y) =
      if Pairwise (fun i i' => (w i).val.Coprime (w i').val) then
        ∑z:SupportedHistory S j [],
          unitPivotOutgoing k j hj width ζ χ a w y
            (historyRowTag k j (positiveTupleProduct w) (copiedSampleState (schedule k j) j width h) z.val.1)*
          RetainedRow.term k j B V extra mask X Δ W (positiveTupleProduct w)
            (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
            z.val (unitRetainedPhase k j hj width ζ χ a h y (positiveTupleProduct w) z.val.1 z.val.2)
      else 0 := by
  have hterm := fun z:SupportedHistory S j [] => retained_source_summand_of_sample k j hj width χ a
    B V extra mask X Δ W w h y z.val.1 z.val.2 hχ (ht z)
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun z _ => hterm z)
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero] at hs
  unfold unitAmplitudeIntegrand
  rw [show amplitudeIntegrand k j width χ a B V extra mask X Δ W S
      (scheduledSample k j hj width w h y)=_ from hs]
  rw [sampleUnitMultiplier_scheduledSample]
  split_ifs
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [unitPivotOutgoing,unitRetainedPhase,RetainedRow.term]
    ring
  · exact mul_zero _

end Ostmann.Characters.Template

end

end OAI
