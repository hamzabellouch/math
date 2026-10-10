import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePairTerm
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitPairAlgebra

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def reindexedCanonicalUnitPairTerm (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (ζ:PrimeUnitData (schedule k j) width Q)
    (χ:PrimeCharacterData (schedule k j) width Q)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (s v w:ℤ) (tL tR:HistoryReconstruction.Tree j) : ℂ :=
  (survivorUnitMultiplier (schedule k j) j width ζ hL y *
    conj (survivorUnitMultiplier (schedule k j) j width ζ hR y)) *
  reindexedCanonicalPairTerm k j hj width χ a B V R leafMask X Δ W hL hR y s v w tL tR

theorem reindexedCanonicalUnitPairTerm_eq (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (ζ:PrimeUnitData (schedule k j) width Q) (hζ:∀i p,‖ζ i p‖=1)
    (χ:PrimeCharacterData (schedule k j) width Q) (hχ:∀i p,χ i p≠1)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (s v w:ℤ) (tL tR:HistoryReconstruction.Tree j)
    (ht:∀i,HistoryFrequencyUnits (nextSample (schedule k j) j width hL hR y i).val
      (j+1) s ((v,w),tL,tR))
    (hlarge:∀i,∀q:ℕ,Nat.Prime q → q∣(pairedState k j
      (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y) i).natAbs → s.natAbs<q)
    (hPB:∀P∈R j,(P:ℤ)≤B j (pairedState k j
      (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y)))
    (hv:|v|≤V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)))
    (hw:|w|≤V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)))
    (hgap:2*B j (pairedState k j (copiedSampleState (schedule k j) j width hL)
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
    reindexedCanonicalPairTerm_eq k j hj width χ hχ a B V R leafMask X Δ W hL hR y s v w tL tR
      ht hlarge hPB hv hw hgap,
    survivorUnitMultiplier_pair (schedule k j) j width ζ hζ hL hR y]
  split_ifs
  · simp only [unitHistoryPhase]
    ring
  · exact mul_zero _

theorem frequencyPairCoefficient_eq_unitPairTerm (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (ζ:PrimeUnitData (schedule k j) width Q)
    (χ:PrimeCharacterData (schedule k j) width Q)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (S:List Bool→Finset ℤ) (T:Finset ℤ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (z z':SupportedHistory S j []) (s:ℤ) :
    RetainedRow.frequencyPairCoefficient k j B V (canonicalHistoryExtra k R)
      (canonicalHistoryMask k leafMask) X Δ W
      (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width)
      S [] (R j)
      (fun y P h z => unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2)
      T y hL hR z z' s =
    reindexedCanonicalUnitPairTerm k j hj width ζ χ a B V R leafMask X Δ W hL hR y
      s z.val.1 z'.val.1 z.val.2 z'.val.2 := by
  change RetainedRow.frequencyPairCoefficient k j B V (canonicalHistoryExtra k R)
    (canonicalHistoryMask k leafMask) X Δ W _ _ S [] (R j)
    (fun y P h z => survivorUnitMultiplier (schedule k j) j width ζ h y *
      sampledRetainedPhase k j hj width χ a h y P z.val.1 z.val.2) T y hL hR z z' s = _
  rw [RetainedRow.frequencyPairCoefficient_mul]
  rfl

end Ostmann.Characters.Template

end

end OAI
