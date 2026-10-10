import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePairTermSampleSupported
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitPairTerm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem reindexedCanonicalUnitPairTerm_eq_of_sample_support (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (ζ:PrimeUnitData (schedule k j) width Q) (hζ:∀i p,‖ζ i p‖=1)
    (χ:PrimeCharacterData (schedule k j) width Q)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (s v w:ℤ) (tL tR:HistoryReconstruction.Tree j)
    (hχ:∀i,χ (previousConstituent (schedule k j) j width i)
      (nextSample (schedule k j) j width hL hR y i)≠1)
    (ht:∀i,HistoryFrequencyUnits (nextSample (schedule k j) j width hL hR y i).val
      (j+1) s ((v,w),tL,tR))
    (hlarge:∀i,∀q:ℕ,Nat.Prime q → q∣(pairedState k j
      (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y) i).natAbs → s.natAbs<q)
    (hBounds : ∀P∈R j,
      retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W j v (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width hL)
          (outsideSampleState (schedule k j) j width y)) tL≠0 →
      retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W j w (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width hR)
          (outsideSampleState (schedule k j) j width y)) tR≠0 →
      (P:ℤ)≤B j (pairedState k j (copiedSampleState (schedule k j) j width hL)
        (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)) ∧
      |v|≤V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
        (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)) ∧
      |w|≤V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
        (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)) ∧
      2*B j (pairedState k j (copiedSampleState (schedule k j) j width hL)
        (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y))*
      V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
        (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y))<
      ∏i,copiedSampleState (schedule k j) j width hR i) :
    reindexedCanonicalUnitPairTerm k j hj width ζ χ a B V R leafMask X Δ W hL hR y s v w tL tR =
      if samplePrimeSupport (schedule k (j+1)) width (nextSample (schedule k j) j width hL hR y) then
        retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
          X Δ W (j+1) s (pairedState k j (copiedSampleState (schedule k j) j width hL)
            (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y))
          ((v,w),tL,tR) *
        unitHistoryPhase k (j+1) width (nextUnitData (schedule k j) j width ζ)
          (fun i => χ (previousConstituent (schedule k j) j width i))
          (fun i => a (previousConstituent (schedule k j) j width i))
          (nextSample (schedule k j) j width hL hR y) s ((v,w),tL,tR)
      else 0 := by
  rw [reindexedCanonicalUnitPairTerm,
    reindexedCanonicalPairTerm_eq_of_sample_support k j hj width χ a B V R leafMask X Δ W hL hR y s v w tL tR
      hχ ht hlarge hBounds,
    survivorUnitMultiplier_pair (schedule k j) j width ζ hζ hL hR y]
  split_ifs
  · simp only [unitHistoryPhase]
    ring
  · exact mul_zero _

end Ostmann.Characters.Template

end

end OAI
