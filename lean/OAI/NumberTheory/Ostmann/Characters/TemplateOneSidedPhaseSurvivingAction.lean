import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingPair

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

def copiedSurvivingPermutation (k j : ℕ) (width : Role→ℕ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    Equiv.Perm (SurvivingPrimeIndex k j width) :=
  Equiv.sumCongr σ (Equiv.refl _)

@[simp] theorem copiedSurvivingPermutation_copied (k j : ℕ) (width : Role→ℕ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (i : CopiedConstituent (schedule k j) j width) :
    copiedSurvivingPermutation k j width σ (.inl i)=.inl (σ i) := rfl

@[simp] theorem copiedSurvivingPermutation_outside (k j : ℕ) (width : Role→ℕ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (i : OutsideConstituent (schedule k j) j width) :
    copiedSurvivingPermutation k j width σ (.inr i)=.inr i := rfl

theorem copiedSurvivingPermutation_old (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (i : SurvivingPrimeIndex k j width) :
    scheduledConstituentInput k j hj width (.inr (copiedSurvivingPermutation k j width σ i)) =
      copiedPermutationExtension (schedule k j) j width σ
        (scheduledConstituentInput k j hj width (.inr i)) := by
  cases i with
  | inl i => exact (copiedPermutationExtension_copied _ _ _ _ _).symm
  | inr i => exact (copiedPermutationExtension_outside _ _ _ _ _).symm

theorem survivingDifferenceGraph_copied (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (i h : SurvivingPrimeIndex k j width) :
    survivingDifferenceGraph k j hj width (copiedSurvivingPermutation k j width σ)
      (copiedSurvivingPermutation k j width ρ) i h =
    differenceGraph k j width (copiedPermutationExtension (schedule k j) j width σ)
      (copiedPermutationExtension (schedule k j) j width ρ)
      (scheduledConstituentInput k j hj width (.inr i))
      (scheduledConstituentInput k j hj width (.inr h)) := by
  simp only [survivingDifferenceGraph,survivingGraph,permutedGraph,differenceGraph,
    copiedSurvivingPermutation_old]

theorem copied_changed_code_surviving_edge {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j<k) (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : CopiedBulkPreserving cfg m j σ) (hρ : CopiedBulkPreserving cfg m j ρ)
    (z : Word k j × Fin m)
    (hc : bulkCode k j m (copiedBulkImage cfg m j σ hσ z) ≠
      bulkCode k j m (copiedBulkImage cfg m j ρ hρ z)) :
    ∃a : Fin j, ∃b : Bool,
      let D := survivingDifferenceGraph k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ)
      let L : SurvivingPrimeIndex k j (sourceWidth cfg m) := .inl (copiedBulk cfg m j z)
      let S : SurvivingPrimeIndex k j (sourceWidth cfg m) := .inr (copiedRetiredOutside cfg m j hj.le false a b)
      let B : SurvivingPrimeIndex k j (sourceWidth cfg m) := .inr (copiedRetiredOutside cfg m j hj.le true a b)
      L≠S ∧ L≠B ∧
        (((D S L=2 ∨ D S L = -2) ∧ D L S=0) ∨
         ((D L B=2 ∨ D L B = -2) ∧ D B L=0)) := by
  obtain ⟨a,b,hne,hne',he⟩ := copied_changed_code_edge cfg m j hj.le σ ρ hσ hρ z hc
  refine ⟨a,b,Sum.inl_ne_inr,Sum.inl_ne_inr,?_⟩
  simpa only [survivingDifferenceGraph_copied,scheduledConstituentInput,
    constituentInputEquiv_copied,constituentInputEquiv_outside,copiedRetiredOutside_old,copiedBulkOld] using he

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
