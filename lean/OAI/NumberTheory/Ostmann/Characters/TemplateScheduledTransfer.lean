import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnitsNorms
import OAI.NumberTheory.Ostmann.Characters.TemplateScheduledAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalFrequency

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem scheduledUnitAmplitude_transfer (k j : ℕ) (hj : j<k) (width : Role → ℕ) {Q : ℕ}
    (E0 : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE0 : ∀i,0<primeShellMass (E0 i))
    (ζ0 : PrimeUnitData (schedule k 0) width Q) (hζ0 : ∀i p,‖ζ0 i p‖=1)
    (χ0 : PrimeCharacterData (schedule k 0) width Q) (hχ0 : ∀i p,p∈E0 i→χ0 i p≠1)
    (a0 : PrimeTranslationData (schedule k 0) width Q)
    (B V : (l : ℕ) → State k (l+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X rate m W : ℝ)
    (hrate : 0 ≤ rate) (hm : 1 ≤ m)
    (hU : ∀i p,p∈E0 i→terminalFrequencyCutoff rate m (j+1)<p.val)
    (hBounds:∀y,(outsidePrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hR≠0→
      ∀z z':SupportedHistory (ranges rate m j) j [],canonicalPairBounds k j width B V R leafMask X (rate*m) W
        hL hR y z.val.1 z'.val.1 z.val.2 z'.val.2)
    (Hmax Pmin:ℝ)
    (hcopied:∀y,(outsidePrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hR≠0→
      ∀(z z':SupportedHistory (ranges rate m j) j []),∀P∈R j,
      RetainedRow.pairCoefficient k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X (rate*m) W (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width)
        (ranges rate m j) [] (fun y P h z=>unitRetainedPhase k j hj width (scheduledUnitData k width ζ0 j) (scheduledCharacterData k width χ0 j) (scheduledTranslationData k width a0 j) h y P z.val.1 z.val.2)
        y hL hR z z' P≠0→
      |((∏i,copiedSampleState (schedule k j) j width hL i:ℤ):ℝ)|≤Hmax ∧
      |((∏i,copiedSampleState (schedule k j) j width hR i:ℤ):ℝ)|≤Hmax)
    (hPmin:0<Pmin) (hpivot:∀P∈R j,Pmin≤(P:ℝ))
    (hcap:2*(bound rate m j : ℝ)*Hmax≤((bound rate m (j+1) : ℤ):ℝ)*Pmin)
    (hR:∀w:PivotProductFibers.PrimeTuple Q (width ((schedule k j).role (pivotSlot k j hj).val)),
      (∀i,w i∈(scheduledPrimeShells k width E0 j) ⟨(pivotSlot k j hj).val,i⟩)→PivotEliminationActual.positiveTupleProduct w∈R j) :
    ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j‖^2 ≤
      scheduledPivotFactor k width E0 j hj *
        (scheduledUnitDiagonal k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj +
          ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W (j+1)‖) := by
  have hF : ∀path f,
      f∈stepHistoryRanges (ranges rate m j)
        ((Finset.Icc (-(bound rate m (j+1):ℤ)) (bound rate m (j+1):ℤ)).erase 0) path →
      f≠0 ∧ f.natAbs≤terminalFrequencyCutoff rate m (j+1) := by
    change ∀path f,f∈stepHistoryRanges (ranges rate m j)
      (signedRange (bound rate m (j+1))) path → _
    rw [stepHistoryRanges_actual]
    exact ranges_le_terminalFrequencyCutoff hrate hm (j+1)
  have hfrequency : ∀v∈ranges rate m j [],|(v:ℝ)|≤(bound rate m j:ℝ) := by
    intro v hv
    have hv' := (mem_signedRange (bound rate m j) v).mp hv
    have habs : |v|≤(bound rate m j:ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hv'.2
    exact_mod_cast habs
  have he := unitAmplitude_transfer k j hj width
    (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)
    (scheduledUnitData k width ζ0 j) (norm_scheduledUnitData k width ζ0 hζ0 j)
    (scheduledCharacterData k width χ0 j) (scheduledCharacterData_nonprincipal k j width E0 χ0 hχ0)
    (scheduledTranslationData k width a0 j) B V R leafMask X (rate*m) W
    (ranges rate m j) (bound rate m (j+1):ℤ) (terminalFrequencyCutoff rate m (j+1))
    (scheduledPrimeShells_source_prime_gt k j width E0 hU) hF hBounds
    (bound rate m j:ℝ) Hmax Pmin hfrequency hcopied hPmin hpivot hcap hR
  change _ ≤ _ * (_ + ‖unitAmplitude _ _ _ _ _ _ _ _ _ _ _ _ _
    (stepHistoryRanges (ranges rate m j) (signedRange (bound rate m (j+1)))) _ _‖) at he
  rw [stepHistoryRanges_actual] at he
  exact he

end Ostmann.Characters.Template

end

end OAI
