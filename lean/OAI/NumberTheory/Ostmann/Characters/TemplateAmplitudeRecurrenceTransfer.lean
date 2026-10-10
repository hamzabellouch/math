import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceOffDiagonalBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem unitAmplitude_transfer (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
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
    (hcap:2*Vmax*Hmax≤(Uroot:ℝ)*Pmin)
    (hR:∀w:PivotProductFibers.PrimeTuple Q (width ((schedule k j).role (pivotSlot k j hj).val)),
      (∀i,w i∈E ⟨(pivotSlot k j hj).val,i⟩)→PivotEliminationActual.positiveTupleProduct w∈R j) :
    ‖unitAmplitude k j width ζ χ a B V (canonicalHistoryExtra k R)
      (canonicalHistoryMask k leafMask) X Δ W S E hE‖^2 ≤
      (((width ((schedule k j).role (pivotSlot k j hj).val)).factorial:ℝ)*
        PivotProductFibers.normalization (fun i=>E ⟨(pivotSlot k j hj).val,i⟩))*
      (unitDiagonal k j hj width E hE ζ χ a B V (canonicalHistoryExtra k R)
        (canonicalHistoryMask k leafMask) X Δ W S (R j)+‖
    unitAmplitude k (j+1) width (nextUnitData (schedule k j) j width ζ)
      (fun i=>χ (previousConstituent (schedule k j) j width i))
      (fun i=>a (previousConstituent (schedule k j) j width i))
      B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X Δ W
      (stepHistoryRanges S ((Finset.Icc (-Uroot) Uroot).erase 0)) (nextPrimeShells (schedule k j) j width E)
      (nextPrimeShells_positive (schedule k j) j width E hE)‖) := by
  have hOld:∀path f,f∈S path→f≠0 ∧ f.natAbs≤U := by
    intro path f hf
    exact hF (path++[false]) f (by simpa only [stepHistoryRanges_append] using hf)
  have he:=unitAmplitude_sq_le_diagonal_offDiagonal k j hj width E hE ζ χ a B V
    (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X Δ W S (R j)
    hζ hχ U hU hOld hR
  rw [unitOffDiagonal_eq_nextAmplitude_of_bounds k j hj width E hE ζ hζ χ hχ a B V R leafMask
    X Δ W S Uroot U hU hF hBounds Vmax Hmax Pmin hfrequency hcopied hPmin hpivot hcap] at he
  exact he

end Ostmann.Characters.Template

end

end OAI
