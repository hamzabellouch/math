import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceCanonical
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceLabels
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def canonicalPairBounds (k j:ℕ) (width:Role→ℕ) {Q:ℕ}
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (v w:ℤ) (tL tR:HistoryReconstruction.Tree j) : Prop :=
∀P∈R j,
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
      ∏i,copiedSampleState (schedule k j) j width hR i

theorem supportedHistory_root_mem {S:List Bool→Finset ℤ} {j:ℕ} {path:List Bool}
    (z:SupportedHistory S j path) : z.val.1∈S path := by
  cases j with
  | zero => exact z.property
  | succ j => exact z.property.1

end Ostmann.Characters.Template

end

end OAI
