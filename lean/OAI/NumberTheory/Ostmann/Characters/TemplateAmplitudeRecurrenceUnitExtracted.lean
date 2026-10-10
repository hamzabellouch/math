import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceEnergy
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceShellSource

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)

def unitExtractedAmplitude : ℂ :=
  (outsidePrimePrior (schedule k j) j width E hE).cmean (fun y =>
  (pivotPrimePrior k j hj width E hE).cmean (fun w =>
    if Pairwise (fun i i' => (w i).val.Coprime (w i').val) then
    (copiedPrimePrior (schedule k j) j width E hE).cmean (fun h =>
      ∑z:SupportedHistory S j [],
        unitPivotOutgoing k j hj width ζ χ a w y
          (historyRowTag k j (positiveTupleProduct w) (copiedSampleState (schedule k j) j width h) z.val.1)*
        RetainedRow.term k j B V extra mask X Δ W (positiveTupleProduct w)
          (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
          z.val (unitRetainedPhase k j hj width ζ χ a h y (positiveTupleProduct w) z.val.1 z.val.2))
    else 0))

theorem unitExtractedAmplitude_sq_le_energy (hζ : ∀i p,‖ζ i p‖=1) (hχ : ∀i p,p∈E i→χ i p≠1) (R : Finset ℕ+)
    (hR : ∀w : PrimeTuple Q (width ((schedule k j).role (pivotSlot k j hj).val)),
      (∀i,w i∈E ⟨(pivotSlot k j hj).val,i⟩) → positiveTupleProduct w∈R) :
    ‖unitExtractedAmplitude k j hj width E hE ζ χ a B V extra mask X Δ W S‖^2 ≤
      (((width ((schedule k j).role (pivotSlot k j hj).val)).factorial:ℝ)*
        PivotProductFibers.normalization (fun i => E ⟨(pivotSlot k j hj).val,i⟩))*
      RetainedRow.energy k j B V extra mask X Δ W
        (copiedPrimePrior (schedule k j) j width E hE)
        (outsidePrimePrior (schedule k j) j width E hE)
        (copiedSampleState (schedule k j) j width)
        (outsideSampleState (schedule k j) j width) S [] R
        (fun y P h z => unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2) := by
  have hh := history_pivot_elimination k j
    (fun i => E ⟨(pivotSlot k j hj).val,i⟩) (fun i => hE ⟨(pivotSlot k j hj).val,i⟩)
    (copiedPrimePrior (schedule k j) j width E hE)
    (outsidePrimePrior (schedule k j) j width E hE)
    (copiedSampleState (schedule k j) j width)
    (outsideSampleState (schedule k j) j width) S [] mask X Δ W R
    (fun w _ => Pairwise (fun i i' => (w i).val.Coprime (w i').val))
    (fun w hw _ _ => hR w hw)
    (unitPivotOutgoing k j hj width ζ χ a)
    (fun y P h z => RetainedRow.guardPhase k j B V extra P
      (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
      z.val (unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2))
    (fun w hw y _ u => norm_unitPivotOutgoing_le_of_sample k j hj width ζ hζ χ a w y u
      (fun i => hχ _ _ (hw i)))
  simpa only [unitExtractedAmplitude,pivotPrimePrior,RetainedRow.energy,
    RetainedRow.grouped_eq,←RetainedRow.term_eq] using hh

end
end Ostmann.Characters.Template

end

end OAI
