import OAI.NumberTheory.Ostmann.Characters.PivotEliminationActualSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateActualPhaseSplit
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual
attribute [local instance] Classical.propDecidable

def sampledPivotOutgoing (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (u : ZMod (positiveTupleProduct w:ℕ)) : ℂ :=
  letI : ∀i, Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
  actualPivotOutgoing k j hj width (fun i => (w i).val)
    (fun i => χ ((scheduledConstituentInput k j hj width) (.inl i)) (w i))
    (fun i => a ((scheduledConstituentInput k j hj width) (.inl i)) (w i))
    (∏i,(y i).val) u

def sampledPivotSurviving (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  let z := Sum.elim h y
  letI : ∀i, Fact (z i).val.Prime := fun i => ⟨primeUpTo_prime (z i)⟩
  actualPivotSurviving k j hj width (fun i => (z i).val)
    (fun i => χ ((scheduledConstituentInput k j hj width) (.inr i)) (z i))
    (fun i => a ((scheduledConstituentInput k j hj width) (.inr i)) (z i)) P s t

theorem norm_sampledPivotOutgoing_le (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀i p,χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (u : ZMod (positiveTupleProduct w:ℕ)) :
    ‖sampledPivotOutgoing k j hj width χ a w y u‖≤1 := by
  let : ∀i, Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
  exact norm_actualPivotOutgoing_le k j hj width _ _ (fun i => hχ _ _) _ _ _

theorem prod_copiedSampleState (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q) :
    (∏i,copiedSampleState (schedule k j) j width h i) = ((∏i,(h i).val:ℕ):ℤ) := by
  simp only [copiedSampleState,Nat.cast_prod]
  exact (Fintype.prod_sigma (fun i => ((h i).val:ℤ))).symm

theorem groupedPivotResidue_eq_historyRowTag (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (hc : (∏i,(h i).val).Coprime (∏i,(w i).val)) (s : ℤ) :
    groupedPivotResidue (fun i => (w i).val) (∏i,(h i).val) hc s =
      historyRowTag k j (positiveTupleProduct w) (copiedSampleState (schedule k j) j width h) s := by
  simp only [groupedPivotResidue,historyRowTag,prod_copiedSampleState,Int.cast_natCast]
  congr 1

end Ostmann.Characters.Template

end

end OAI
