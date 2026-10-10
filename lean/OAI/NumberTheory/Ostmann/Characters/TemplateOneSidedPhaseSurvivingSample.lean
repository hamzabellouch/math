import OAI.NumberTheory.Ostmann.Characters.SourceTemplateCopiedData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSampleBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem unitRetainedPhase_copied_permutation (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (hχ : ∀i p,χ (copiedPermutationExtension (schedule k j) j width σ.symm i) p=χ i p)
    (ha : ∀i p,a (copiedPermutationExtension (schedule k j) j width σ.symm i) p=a i p)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hc : Pairwise (fun i z => (Sum.elim h y i).val.Coprime (Sum.elim h y z).val))
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    letI : ∀i,Fact (Sum.elim h y i).val.Prime := fun i => ⟨primeUpTo_prime (Sum.elim h y i)⟩
    unitRetainedPhase k j hj width ζ χ a (fun i=>h (σ.symm i)) y P s t =
      decoratedSurvivingPhase k j hj width (copiedSurvivingPermutation k j width σ)
        (fun i => (Sum.elim h y i).val)
        (finiteSurvivingCharacters k j hj width χ) (finiteSurvivingTranslations k j hj width a)
        (finiteSurvivingUnits k j hj width ζ) P s t := by
  let τ := copiedSurvivingPermutation k j width σ
  have he : (fun i => Sum.elim h y (τ.symm i)) = Sum.elim (fun i=>h (σ.symm i)) y := by
    funext i
    cases i <;> rfl
  have hcp : Pairwise (fun i z => (Sum.elim (fun i=>h (σ.symm i)) y i).val.Coprime
      (Sum.elim (fun i=>h (σ.symm i)) y z).val) := by
    rw [←he]
    intro i z hn
    exact hc (fun hh=>hn (τ.symm.injective hh))
  rw [unitRetainedPhase_eq_sampledDecoratedSurvivor k j hj width ζ χ a _ y hcp P s t]
  rw [←he]
  apply (decoratedSurvivingPhase_eq_sampled k j hj width ζ χ a τ (Sum.elim h y) ?_ ?_ P s t).symm
  · intro i p
    change χ (scheduledConstituentInput k j hj width
      (.inr (copiedSurvivingPermutation k j width σ.symm i))) p = _
    rw [copiedSurvivingPermutation_old]
    exact hχ _ p
  · intro i p
    change a (scheduledConstituentInput k j hj width
      (.inr (copiedSurvivingPermutation k j width σ.symm i))) p = _
    rw [copiedSurvivingPermutation_old]
    exact ha _ p

theorem source_unitRetainedPhase_copied_permutation {k Q : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) Q)
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hc : Pairwise (fun i z => (Sum.elim h y i).val.Coprime (Sum.elim h y z).val))
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j
    let ad := scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j
    letI : ∀i,Fact (Sum.elim h y i).val.Prime := fun i => ⟨primeUpTo_prime (Sum.elim h y i)⟩
    unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad (fun i=>h (σ.symm i)) y P s t =
      decoratedSurvivingPhase k j hj (sourceWidth cfg m) (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (fun i => (Sum.elim h y i).val)
        (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χd)
        (finiteSurvivingTranslations k j hj (sourceWidth cfg m) ad)
        (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) P s t :=
  unitRetainedPhase_copied_permutation k j hj (sourceWidth cfg m) ζ _ _ σ
    (source_copied_characters cfg m j χ σ.symm) (source_copied_centers cfg m j a σ.symm) h y hc P s t

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
