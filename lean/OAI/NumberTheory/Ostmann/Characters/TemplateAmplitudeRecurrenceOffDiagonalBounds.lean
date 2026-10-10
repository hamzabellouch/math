import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceCutoffBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceOffDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem unitOffDiagonal_eq_nextAmplitude_of_bounds (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (E:(schedule k j).Constituent width→Finset (PrimeUpTo Q))
    (hE:∀i,0<primeShellMass (E i))
    (ζ:PrimeUnitData (schedule k j) width Q) (hζ:∀i p,‖ζ i p‖=1)
    (χ:PrimeCharacterData (schedule k j) width Q) (hχ:∀i p,p∈E i→χ i p≠1)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (S:List Bool→Finset ℤ) (Uroot:ℤ) (U:ℕ)
    (hU:∀i p,p∈E i→U<p.val)
    (hF:∀path f,f∈stepHistoryRanges S ((Finset.Icc (-Uroot) Uroot).erase 0) path→f≠0 ∧ f.natAbs≤U)
    (hBounds:∀y,(outsidePrimePrior (schedule k j) j width E hE).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width E hE).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width E hE).mass hR≠0→
      ∀z z':SupportedHistory S j [],canonicalPairBounds k j width B V R leafMask X Δ W
        hL hR y z.val.1 z'.val.1 z.val.2 z'.val.2)
    (Vmax Hmax Pmin:ℝ)
    (hfrequency:∀v∈S [],|(v:ℝ)|≤Vmax)
    (hcopied:∀y,(outsidePrimePrior (schedule k j) j width E hE).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width E hE).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width E hE).mass hR≠0→
      ∀(z z':SupportedHistory S j []),∀P∈R j,
      RetainedRow.pairCoefficient k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width)
        S [] (fun y P h z=>unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2)
        y hL hR z z' P≠0→
      |((∏i,copiedSampleState (schedule k j) j width hL i:ℤ):ℝ)|≤Hmax ∧
      |((∏i,copiedSampleState (schedule k j) j width hR i:ℤ):ℝ)|≤Hmax)
    (hPmin:0<Pmin) (hpivot:∀P∈R j,Pmin≤(P:ℝ))
    (hcap:2*Vmax*Hmax≤(Uroot:ℝ)*Pmin) :
    unitOffDiagonal k j hj width E hE ζ χ a B V (canonicalHistoryExtra k R)
      (canonicalHistoryMask k leafMask) X Δ W S (R j) =
    unitAmplitude k (j+1) width (nextUnitData (schedule k j) j width ζ)
      (fun i=>χ (previousConstituent (schedule k j) j width i))
      (fun i=>a (previousConstituent (schedule k j) j width i))
      B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X Δ W
      (stepHistoryRanges S ((Finset.Icc (-Uroot) Uroot).erase 0)) (nextPrimeShells (schedule k j) j width E)
      (nextPrimeShells_positive (schedule k j) j width E hE) := by
  apply unitOffDiagonal_eq_nextAmplitude k j hj width E hE ζ hζ χ hχ a B V R leafMask
    X Δ W S ((Finset.Icc (-Uroot) Uroot).erase 0) U hU hF hBounds
  intro y hy hL hR hLm hRm z z' P hP s hN he hf
  obtain ⟨hHL,hHR⟩ := hcopied y hy hL hR hLm hRm z z' P hP hf
  exact reversal_frequency_mem_erase_Icc hN he
    (hfrequency _ (supportedHistory_root_mem z)) (hfrequency _ (supportedHistory_root_mem z'))
    hHL hHR hPmin (hpivot P hP) hcap

end Ostmann.Characters.Template

end

end OAI
