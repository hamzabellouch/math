import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorSources
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePhase
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

abbrev PrimeCharacterData (T : Layout) (width : Role → ℕ) (Q : ℕ) :=
  (i : T.Constituent width) → (p : PrimeUpTo Q) → MulChar (ZMod p.val) ℂ

abbrev PrimeTranslationData (T : Layout) (width : Role → ℕ) (Q : ℕ) :=
  (i : T.Constituent width) → (p : PrimeUpTo Q) → ZMod p.val

def sampledHistoryPhase (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (x : (schedule k j).Constituent width → PrimeUpTo Q)
    (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  letI : ∀i, Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  actualHistoryPhase k j width (fun i => (x i).val)
    (fun i => χ i (x i)) (fun i => a i (x i)) s t

def samplePrimeSupport (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) : Prop :=
  Pairwise (fun i h => (x i).val.Coprime (x h).val)

def amplitudeIntegrand (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (x : (schedule k j).Constituent width → PrimeUpTo Q) : ℂ :=
  if samplePrimeSupport (schedule k j) width x then
    ∑ z : SupportedHistory S j [],
      retainedHistoryWeight k B V extra mask X Δ W j z.val.1
        (constituentSampleState (schedule k j) width x) z.val.2 *
      sampledHistoryPhase k j width χ a x z.val.1 z.val.2
  else 0

def actualAmplitude (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) : ℂ :=
  (constituentPrimePrior (schedule k j) width E hE).cmean
    (amplitudeIntegrand k j width χ a B V extra mask X Δ W S)

theorem actualAmplitude_disintegration (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) :
    actualAmplitude k j width E hE χ a B V extra mask X Δ W S =
      (outsidePrimePrior (schedule k j) j width E hE).cmean (fun y =>
      (pivotPrimePrior k j hj width E hE).cmean (fun w =>
      (copiedPrimePrior (schedule k j) j width E hE).cmean (fun h =>
        amplitudeIntegrand k j width χ a B V extra mask X Δ W S
          (scheduledSample k j hj width w h y)))) :=
  scheduled_constituentPrimePrior_cmean k j hj width E hE _

theorem sampledHistoryPhase_zero (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k 0) width Q)
    (a : PrimeTranslationData (schedule k 0) width Q)
    (x : (schedule k 0).Constituent width → PrimeUpTo Q)
    (s : ℤ) (t : HistoryReconstruction.Tree 0) :
    sampledHistoryPhase k 0 width χ a x s t =
      letI : ∀i, Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
      initialPhase (fun i => (x i).val) (fun i => χ i (x i)) (fun i => a i (x i)) s := by
  let : ∀i, Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  exact actualHistoryPhase_zero k width _ _ _ s t

end Ostmann.Characters.Template

end

end OAI
