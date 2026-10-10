import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSupportSamples

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem samplePrimeSupport_iff (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) :
    samplePrimeSupport T width x ↔
      Pairwise (fun i h => IsCoprime
        (constituentSampleState T width x i) (constituentSampleState T width x h)) ∧
      withinAtomPrimeSupport T width x :=
  constituent_prime_support_iff T width x

theorem samplePrimeSupport_indicator (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) (z : ℂ) :
    (if samplePrimeSupport T width x then z else 0) =
      (if Pairwise (fun i h => IsCoprime
        (constituentSampleState T width x i) (constituentSampleState T width x h))
        then (1:ℂ) else 0) *
      (if withinAtomPrimeSupport T width x then (1:ℂ) else 0) * z := by
  rw [samplePrimeSupport_iff]
  split_ifs <;> simp_all

theorem scheduledSample_internal_indicator (k j : ℕ) (hj : j < k)
    (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) (z : ℂ) :
    (if withinAtomPrimeSupport (schedule k j) width (scheduledSample k j hj width w h y)
      then z else 0) =
      (if Pairwise (fun a b => (w a).val.Coprime (w b).val) then (1:ℂ) else 0) *
      (if copiedWithinAtomPrimeSupport (schedule k j) j width h then (1:ℂ) else 0) *
      (if outsideWithinAtomPrimeSupport (schedule k j) j width y then (1:ℂ) else 0) * z := by
  rw [withinAtomPrimeSupport_scheduledSample]
  split_ifs <;> simp_all

theorem nextSample_internal_indicator (T : Layout) (j : ℕ)
    (width : Role → ℕ) {Q : ℕ}
    (hL hR : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) (z : ℂ) :
    (if withinAtomPrimeSupport (T.step j) width (nextSample T j width hL hR y)
      then z else 0) =
      (if copiedWithinAtomPrimeSupport T j width hL then (1:ℂ) else 0) *
      (if copiedWithinAtomPrimeSupport T j width hR then (1:ℂ) else 0) *
      (if outsideWithinAtomPrimeSupport T j width y then (1:ℂ) else 0) * z := by
  rw [withinAtomPrimeSupport_nextSample]
  split_ifs <;> simp_all

theorem amplitudeIntegrand_atom_support (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (x : (schedule k j).Constituent width → PrimeUpTo Q) :
    amplitudeIntegrand k j width χ a B V extra mask X Δ W S x =
      (if Pairwise (fun i h => IsCoprime
        (constituentSampleState (schedule k j) width x i)
        (constituentSampleState (schedule k j) width x h)) then (1:ℂ) else 0) *
      (if withinAtomPrimeSupport (schedule k j) width x then (1:ℂ) else 0) *
      (∑ z : HistoryFrequencyLabels.SupportedHistory S j [],
        retainedHistoryWeight k B V extra mask X Δ W j z.val.1
          (constituentSampleState (schedule k j) width x) z.val.2 *
        sampledHistoryPhase k j width χ a x z.val.1 z.val.2) :=
  samplePrimeSupport_indicator (schedule k j) width x _

end Ostmann.Characters.Template

end

end OAI
