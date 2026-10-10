import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceShellSource
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitExtracted
import OAI.NumberTheory.Ostmann.Construction.JoinedRemaining

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

theorem unitAmplitude_eq_extracted (hχ : ∀i p,p∈E i→χ i p≠1) (U:ℕ)
    (hU : ∀i p,p∈E i → U<p.val)
    (hS : ∀path f,f∈S path → f≠0 ∧ f.natAbs≤U) :
    unitAmplitude k j width ζ χ a B V extra mask X Δ W S E hE =
      unitExtractedAmplitude k j hj width E hE ζ χ a B V extra mask X Δ W S := by
  rw [unitAmplitude_disintegration k j width ζ χ a B V extra mask X Δ W S hj]
  unfold unitExtractedAmplitude
  apply FinitePrior.cmean_congr_support
  intro y hy
  apply FinitePrior.cmean_congr_support
  intro w hw
  have point (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
      (hh : (copiedPrimePrior (schedule k j) j width E hE).mass h≠0) :
      unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S (scheduledSample k j hj width w h y)=
        if Pairwise (fun i i' => (w i).val.Coprime (w i').val) then
          ∑z:SupportedHistory S j [],
            unitPivotOutgoing k j hj width ζ χ a w y
              (historyRowTag k j (positiveTupleProduct w) (copiedSampleState (schedule k j) j width h) z.val.1)*
            RetainedRow.term k j B V extra mask X Δ W (positiveTupleProduct w)
              (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
              z.val (unitRetainedPhase k j hj width ζ χ a h y (positiveTupleProduct w) z.val.1 z.val.2)
        else 0 := by
    have hm : (constituentPrimePrior (schedule k j) width E hE).mass
        (scheduledSample k j hj width w h y)≠0 := by
      rw [scheduled_constituentPrimePrior_mass]
      exact mul_ne_zero (mul_ne_zero hy hw) hh
    exact unitAmplitudeIntegrand_source_of_sample k j hj width ζ χ a B V extra mask X Δ W S w h y
      (fun i => hχ i _ (primeProductPrior_mem_of_mass_ne_zero E hE _ hm i))
      (fun z => constituentPrimePrior_historyFrequencyUnits (schedule k j) width E hE hU _ hm S hS [] z)
  by_cases hp : Pairwise (fun i i' => (w i).val.Coprime (w i').val)
  · rw [ite_eq_left hp]
    apply FinitePrior.cmean_congr_support
    intro h hh
    simpa only [ite_eq_left hp] using point h hh
  · rw [ite_eq_right hp]
    calc
      _ = (copiedPrimePrior (schedule k j) j width E hE).cmean (fun _ => (0:ℂ)) := by
        apply FinitePrior.cmean_congr_support
        intro h hh
        simpa only [ite_eq_right hp] using point h hh
      _ = 0 := by simp only [FinitePrior.cmean,mul_zero,Finset.sum_const_zero]

end
end Ostmann.Characters.Template

end

end OAI
