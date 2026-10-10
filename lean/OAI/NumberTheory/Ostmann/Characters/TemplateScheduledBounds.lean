import OAI.NumberTheory.Ostmann.Characters.PivotProductNormalization
import OAI.NumberTheory.Ostmann.Characters.TemplateScheduledTransfer

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

section
variable (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E0 : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE0 : ∀i,0<primeShellMass (E0 i))
    (ζ0 : PrimeUnitData (schedule k 0) width Q)
    (χ0 : PrimeCharacterData (schedule k 0) width Q)
    (a0 : PrimeTranslationData (schedule k 0) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X rate m W : ℝ)

structure ScheduledTransferBounds (j : ℕ) (hj : j<k) where
  prime_gt : ∀i p,p∈E0 i→terminalFrequencyCutoff rate m (j+1)<p.val
  hBounds:∀y,(outsidePrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hR≠0→
      ∀z z':SupportedHistory (ranges rate m j) j [],canonicalPairBounds k j width B V R leafMask X (rate*m) W
        hL hR y z.val.1 z'.val.1 z.val.2 z'.val.2
  Hmax : ℝ
  Pmin : ℝ
  hcopied:∀y,(outsidePrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E0 j) (scheduledPrimeShells_positive k width E0 hE0 j)).mass hR≠0→
      ∀(z z':SupportedHistory (ranges rate m j) j []),∀P∈R j,
      RetainedRow.pairCoefficient k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X (rate*m) W (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width)
        (ranges rate m j) [] (fun y P h z=>unitRetainedPhase k j hj width (scheduledUnitData k width ζ0 j) (scheduledCharacterData k width χ0 j) (scheduledTranslationData k width a0 j) h y P z.val.1 z.val.2)
        y hL hR z z' P≠0→
      |((∏i,copiedSampleState (schedule k j) j width hL i:ℤ):ℝ)|≤Hmax ∧
      |((∏i,copiedSampleState (schedule k j) j width hR i:ℤ):ℝ)|≤Hmax
  hPmin:0<Pmin
  hpivot:∀P∈R j,Pmin≤(P:ℝ)
  hcap:2*(bound rate m j : ℝ)*Hmax≤((bound rate m (j+1) : ℤ):ℝ)*Pmin
  hR:∀w:PivotProductFibers.PrimeTuple Q (width ((schedule k j).role (pivotSlot k j hj).val)),
      (∀i,w i∈(scheduledPrimeShells k width E0 j) ⟨(pivotSlot k j hj).val,i⟩)→PivotEliminationActual.positiveTupleProduct w∈R j

theorem scheduledUnitAmplitude_transfer_of_bounds (j : ℕ) (hj : j<k)
    (hζ0 : ∀i p,‖ζ0 i p‖=1) (hχ0 : ∀i p,p∈E0 i→χ0 i p≠1)
    (hrate : 0 ≤ rate) (hm : 1 ≤ m)
    (h : ScheduledTransferBounds k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj) :
    ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j‖^2 ≤
      scheduledPivotFactor k width E0 j hj *
        (scheduledUnitDiagonal k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj +
          ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W (j+1)‖) :=
  scheduledUnitAmplitude_transfer k j hj width E0 hE0 ζ0 hζ0 χ0 hχ0 a0 B V R leafMask
    X rate m W hrate hm h.prime_gt h.hBounds h.Hmax h.Pmin h.hcopied h.hPmin h.hpivot h.hcap h.hR

theorem scheduledUnitDiagonal_nonneg (j : ℕ) (hj : j<k) :
    0 ≤ scheduledUnitDiagonal k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj := by
  unfold scheduledUnitDiagonal unitDiagonal
  apply RetainedRow.diagonal_nonneg

include hE0 in
theorem scheduledPivotFactor_pos (j : ℕ) (hj : j<k) :
    0 < scheduledPivotFactor k width E0 j hj := by
  unfold scheduledPivotFactor
  apply mul_pos
  · exact_mod_cast Nat.factorial_pos _
  · exact PivotProductNormalization.normalization_pos _ (fun i =>
      scheduledPrimeShells_positive k width E0 hE0 j _)

end
end Ostmann.Characters.Template

end

end OAI
