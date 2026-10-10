import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateActualPairs
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportPrimes
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (S : List Bool→Finset ℤ) (path : List Bool)

def unitRootRow (y : OutsideConstituent (schedule k j) j width→PrimeUpTo Q) (P : ℕ+)
    (f : CopiedConstituent (schedule k j) j width→PrimeUpTo Q) (s : ↥(S path)) : ℂ :=
  historyRootSum k j S path B V extra mask X Δ W s.val
    (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width f)
      (outsideSampleState (schedule k j) j width y))
    (fun z=>unitRetainedPhase k j hj width ζ χ a f y P z.val.1 z.val.2)

theorem unitRootRow_injective
    (y : OutsideConstituent (schedule k j) j width→PrimeUpTo Q) (P : ℕ+)
    (f : CopiedConstituent (schedule k j) j width→PrimeUpTo Q) (s : ↥(S path))
    (hf : unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P f s≠0) :
    Function.Injective (fun i=>(f i).val) := by
  obtain ⟨z,hz,ht⟩ := historyRootSum_nonzero_term k j S path B V extra mask X Δ W s.val
    (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width f)
      (outsideSampleState (schedule k j) j width y)) _ hf
  exact RetainedRow.unit_term_copiedSample_injective k j hj width ζ χ a B V extra mask X Δ W
    P f y z.val ht

theorem unit_row_diagonal_eq_matching
    (E : (schedule k j).Constituent width→Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (y : OutsideConstituent (schedule k j) j width→PrimeUpTo Q) (P : ℕ+) :
    historyRowDiagonal k j (copiedPrimePrior (schedule k j) j width E hE)
      (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width y)
      S path mask X Δ W P
      (fun f z=>RetainedRow.guardPhase k j B V extra P
        (copiedSampleState (schedule k j) j width f) (outsideSampleState (schedule k j) j width y)
        z.val (unitRetainedPhase k j hj width ζ χ a f y P z.val.1 z.val.2)) =
    matchedRootContribution (fun i=>E (copiedConstituentOld (schedule k j) j width i))
      (fun _i=>hE _) Finset.univ
      (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P) := by
  rw [retained_diagonal_eq_root_pairs]
  simp only [prod_copiedSampleState,Int.natCast_inj]
  exact harmonic_root_pairs_eq_matching (fun i=>E (copiedConstituentOld (schedule k j) j width i))
    (fun i=>hE _) (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P)
    (fun f _ s hs=>unitRootRow_injective k j hj width ζ χ a B V extra mask X Δ W S path y P f s hs)

end

theorem unitDiagonal_eq_matching (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width→Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (ζ : PrimeUnitData (schedule k j) width Q) (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (S : List Bool→Finset ℤ) (R : Finset ℕ+) :
    unitDiagonal k j hj width E hE ζ χ a B V extra mask X Δ W S R =
      (outsidePrimePrior (schedule k j) j width E hE).mean (fun y=>∑P∈R,
        (matchedRootContribution (fun i=>E (copiedConstituentOld (schedule k j) j width i))
          (fun _i=>hE _) Finset.univ
          (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S [] y P)).re) := by
  simp only [unitDiagonal,RetainedRow.diagonal,unit_row_diagonal_eq_matching]

end Ostmann.Characters.DiagonalEstimate

end

end OAI
