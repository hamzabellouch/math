import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSampleDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries
attribute [local instance] Classical.propDecidable

theorem surviving_internal_support (k j : ℕ) (width : Role→ℕ) {Q : ℕ}
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hc : Pairwise (fun i z => (Sum.elim h y i).val.Coprime (Sum.elim h y z).val)) :
    copiedWithinAtomPrimeSupport (schedule k j) j width h ∧
      outsideWithinAtomPrimeSupport (schedule k j) j width y := by
  constructor
  · intro i a b hab
    apply hc (i := .inl ⟨i,a⟩) (j := .inl ⟨i,b⟩)
    intro he
    have hh := Sum.inl.inj he
    have hab' : a=b := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
    exact hab hab'
  · intro i a b hab
    apply hc (i := .inr ⟨i,a⟩) (j := .inr ⟨i,b⟩)
    intro he
    have hh := Sum.inr.inj he
    have hab' : a=b := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
    exact hab hab'

theorem unitRetainedPhase_eq_sampledDecoratedSurvivor (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hc : Pairwise (fun i z => (Sum.elim h y i).val.Coprime (Sum.elim h y z).val))
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    unitRetainedPhase k j hj width ζ χ a h y P s t =
      sampledDecoratedSurvivor k j hj width ζ χ a (Sum.elim h y) P s t := by
  rw [unitRetainedPhase, sampledRetainedPhase, ite_eq_left (surviving_internal_support k j width h y hc)]
  unfold survivorUnitMultiplier sampledPivotSurviving sampledDecoratedSurvivor
  rw [Fintype.prod_sum_type]
  rfl

theorem decoratedSurvivingPhase_eq_sampled (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (τ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (x : SurvivingPrimeIndex k j width → PrimeUpTo Q)
    (hχ : ∀i p,χ (scheduledConstituentInput k j hj width (.inr (τ.symm i))) p =
      χ (scheduledConstituentInput k j hj width (.inr i)) p)
    (ha : ∀i p,a (scheduledConstituentInput k j hj width (.inr (τ.symm i))) p =
      a (scheduledConstituentInput k j hj width (.inr i)) p)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    letI : ∀i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
    decoratedSurvivingPhase k j hj width τ (fun i => (x i).val)
      (finiteSurvivingCharacters k j hj width χ) (finiteSurvivingTranslations k j hj width a)
      (finiteSurvivingUnits k j hj width ζ) P s t =
      sampledDecoratedSurvivor k j hj width ζ χ a (fun i => x (τ.symm i)) P s t := by
  unfold decoratedSurvivingPhase sampledDecoratedSurvivor finiteSurvivingCharacters
    finiteSurvivingTranslations finiteSurvivingUnits
  simp_rw [extendCharacterData_prime, extendTranslationData_prime, extendUnitData_prime, hχ, ha]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
