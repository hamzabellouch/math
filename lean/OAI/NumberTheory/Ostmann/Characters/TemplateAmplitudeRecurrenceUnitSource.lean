import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceActualElimination
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsSplit

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def unitPivotOutgoing (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (u : ZMod (positiveTupleProduct w:ℕ)) : ℂ :=
  pivotUnitMultiplier k j hj width ζ w * sampledPivotOutgoing k j hj width χ a w y u

def unitRetainedPhase (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  survivorUnitMultiplier (schedule k j) j width ζ h y *
    sampledRetainedPhase k j hj width χ a h y P s t

theorem norm_unitPivotOutgoing_le (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀i p,‖ζ i p‖=1)
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀i p,χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (u : ZMod (positiveTupleProduct w:ℕ)) :
    ‖unitPivotOutgoing k j hj width ζ χ a w y u‖≤1 := by
  rw [unitPivotOutgoing,norm_pivotUnitMultiplier_mul k j hj width ζ hζ]
  exact norm_sampledPivotOutgoing_le k j hj width χ hχ a w y u

theorem unitAmplitudeIntegrand_source (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀i p,χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
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
  have hterm := fun z:SupportedHistory S j [] => retained_source_summand k j hj width χ hχ a
    B V extra mask X Δ W w h y z.val.1 z.val.2 (ht z)
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
