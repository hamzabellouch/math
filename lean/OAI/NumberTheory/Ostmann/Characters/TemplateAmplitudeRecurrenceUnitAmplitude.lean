import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsNorms

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def unitHistoryPhase (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (x : (schedule k j).Constituent width → PrimeUpTo Q)
    (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  sampleUnitMultiplier (schedule k j) width ζ x * sampledHistoryPhase k j width χ a x s t

section
variable (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)

def unitAmplitudeIntegrand (x : (schedule k j).Constituent width → PrimeUpTo Q) : ℂ :=
  sampleUnitMultiplier (schedule k j) width ζ x *
    amplitudeIntegrand k j width χ a B V extra mask X Δ W S x

theorem unitAmplitudeIntegrand_eq (x : (schedule k j).Constituent width → PrimeUpTo Q) :
    unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S x =
      if samplePrimeSupport (schedule k j) width x then
        ∑z:SupportedHistory S j [],
          retainedHistoryWeight k B V extra mask X Δ W j z.val.1
            (constituentSampleState (schedule k j) width x) z.val.2 *
          unitHistoryPhase k j width ζ χ a x z.val.1 z.val.2
      else 0 := by
  unfold unitAmplitudeIntegrand amplitudeIntegrand
  split_ifs
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [unitHistoryPhase]
    ring
  · exact mul_zero _

theorem norm_unitAmplitudeIntegrand (hζ : ∀i p,‖ζ i p‖=1)
    (x : (schedule k j).Constituent width → PrimeUpTo Q) :
    ‖unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S x‖ =
      ‖amplitudeIntegrand k j width χ a B V extra mask X Δ W S x‖ := by
  rw [unitAmplitudeIntegrand,norm_mul,norm_sampleUnitMultiplier _ _ ζ hζ,one_mul]

def unitAmplitude (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) : ℂ :=
  (constituentPrimePrior (schedule k j) width E hE).cmean
    (unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S)

theorem unitAmplitude_disintegration (hj:j<k)
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) :
    unitAmplitude k j width ζ χ a B V extra mask X Δ W S E hE =
      (outsidePrimePrior (schedule k j) j width E hE).cmean (fun y =>
      (pivotPrimePrior k j hj width E hE).cmean (fun w =>
      (copiedPrimePrior (schedule k j) j width E hE).cmean (fun h =>
        unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S
          (scheduledSample k j hj width w h y)))) :=
  scheduled_constituentPrimePrior_cmean k j hj width E hE _

end
end Ostmann.Characters.Template

end

end OAI
