import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSourceFactorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual
attribute [local instance] Classical.propDecidable

theorem sampledHistoryPhase_pivot_split (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀i p,χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (w : PivotPrimeIndex k j hj width → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (hc : samplePrimeSupport (schedule k j) width (scheduledSample k j hj width w h y))
    (ht : ∀i,HistoryFrequencyUnits (scheduledSample k j hj width w h y i).val j s t) :
    sampledHistoryPhase k j width χ a (scheduledSample k j hj width w h y) s t =
      sampledPivotOutgoing k j hj width χ a w y
        (historyRowTag k j (positiveTupleProduct w) (copiedSampleState (schedule k j) j width h) s)*
      sampledPivotSurviving k j hj width χ a h y (positiveTupleProduct w) s t := by
  let e := scheduledConstituentInput k j hj width
  let x := scheduledSample k j hj width w h y
  let : ∀i, Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  have he := actualHistoryPhase_pivot_split k j hj width (fun i => (x i).val)
    hc (fun i => χ i (x i)) (fun i => hχ i (x i)) (fun i => a i (x i)) s t ht
  let R (zz:PivotPrimeIndex k j hj width⊕SurvivingPrimeIndex k j width→PrimeUpTo Q)
      (hzz:Pairwise (fun i h => (zz i).val.Coprime (zz h).val)) : ℂ :=
    letI : ∀i,Fact (zz i).val.Prime := fun i => ⟨primeUpTo_prime (zz i)⟩
    actualPivotOutgoing k j hj width (fun i => (zz (.inl i)).val)
      (fun i => χ (e (.inl i)) (zz (.inl i)))
      (fun i => a (e (.inl i)) (zz (.inl i)))
      (inputOutsideProduct (fun i => (zz i).val))
      (groupedPivotResidue (fun i => (zz (.inl i)).val)
        (inputCopiedProduct (fun i => (zz i).val))
        (copiedProduct_coprime_pivot (fun i => (zz i).val) hzz) s)*
    actualPivotSurviving k j hj width (fun i => (zz (.inr i)).val)
      (fun i => χ (e (.inr i)) (zz (.inr i)))
      (fun i => a (e (.inr i)) (zz (.inr i))) (∏i,(zz (.inl i)).val) s t
  have hz : (fun i => x (e i)) = Sum.elim w (Sum.elim h y) := by
    funext i
    simp only [x,e,scheduledSample,assemblePriorSample,Equiv.symm_apply_apply]
  have hcx : Pairwise (fun i h => (x (e i)).val.Coprime (x (e h)).val) :=
    fun _ _ hh => hc (fun he => hh (e.injective he))
  have hcz : Pairwise (fun i z => (Sum.elim w (Sum.elim h y) i).val.Coprime
      (Sum.elim w (Sum.elim h y) z).val) := by
    rw [← hz]
    exact hcx
  have hRgeneral (z1 z2:PivotPrimeIndex k j hj width⊕SurvivingPrimeIndex k j width→PrimeUpTo Q)
      (h1:Pairwise (fun i h => (z1 i).val.Coprime (z1 h).val))
      (h2:Pairwise (fun i h => (z2 i).val.Coprime (z2 h).val))
      (heq:z1=z2) : R z1 h1=R z2 h2 := by
    subst z2
    rfl
  have hR : R (fun i => x (e i)) hcx = R (Sum.elim w (Sum.elim h y)) hcz :=
    hRgeneral _ _ hcx hcz hz
  change sampledHistoryPhase k j width χ a x s t = R (fun i => x (e i)) hcx at he
  refine he.trans (hR.trans ?_)
  dsimp only [R,Sum.elim_inl,Sum.elim_inr,inputCopiedProduct,inputOutsideProduct]
  erw [groupedPivotResidue_eq_historyRowTag k j hj width w h _ s]
  rfl

end Ostmann.Characters.Template

end

end OAI
