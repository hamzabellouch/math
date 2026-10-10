import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateHistoryExpansion
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateUnitMatching

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable (k j : ℕ) (hj : j<k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) (P : ℕ+)

def unitHistoryTerm (f : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (h : SupportedHistory S j path) : ℂ :=
  RetainedRow.term k j B V extra mask X Δ W P
    (copiedSampleState (schedule k j) j width f) (outsideSampleState (schedule k j) j width y)
    h.val (unitRetainedPhase k j hj width ζ χ a f y P h.val.1 h.val.2)

theorem unitRootRow_eq_grouped_history
    (f : CopiedConstituent (schedule k j) j width → PrimeUpTo Q) (s : ↥(S path)) :
    unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P f s =
      ∑h,if historyRootIndex j S path h=s then
        unitHistoryTerm k j hj width ζ χ a B V extra mask X Δ W S path y P f h else 0 := by
  unfold unitRootRow historyRootSum
  apply Finset.sum_congr rfl
  intro h hh
  have he : historyRootIndex j S path h=s ↔ h.val.1=s.val := Subtype.ext_iff
  simp only [he,unitHistoryTerm,RetainedRow.term]

theorem unitRootContribution_eq_normalized_history
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm (CopiedConstituent (schedule k j) j width))) (T D : ℝ) :
    matchedRootContribution (fun i=>E (copiedConstituentOld (schedule k j) j width i))
      (fun _=>hE _) A (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P) =
    ((copiedNormalization (fun i=>E (copiedConstituentOld (schedule k j) j width i))*
      Real.exp (-T-D):ℝ):ℂ)*
      ∑e∈A,∑h,∑h',normalizedHistoryPair
        (fun i=>E (copiedConstituentOld (schedule k j) j width i)) (fun _=>hE _)
        (historyRootIndex j S path)
        (unitHistoryTerm k j hj width ζ χ a B V extra mask X Δ W S path y P) T D e h h' := by
  have he : unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P =
      fun f s=>∑h,if historyRootIndex j S path h=s then
        unitHistoryTerm k j hj width ζ χ a B V extra mask X Δ W S path y P f h else 0 := by
    funext f s
    exact unitRootRow_eq_grouped_history k j hj width ζ χ a B V extra mask X Δ W S path y P f s
  rw [he]
  exact matchedRootContribution_eq_normalized_history _ _ A _ _ T D

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
