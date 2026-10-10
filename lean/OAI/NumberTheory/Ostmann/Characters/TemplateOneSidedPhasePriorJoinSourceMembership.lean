import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinMembership

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem pairedCoordinateMembershipMask_guard {I : Type*} [Fintype I] {A : ℕ}
    (E : I→Finset (PrimeUpTo A)) (σ ρ : Equiv.Perm I) (x : I→PrimeUpTo A)
    (z : ℂ) (C : Prop) [Decidable C] :
    (if C then (∏i,pairedCoordinateMembershipMask E σ ρ i (x i).val)*z else 0) =
      if C ∧ (∀i,x (σ.symm i)∈E i) ∧ (∀i,x (ρ.symm i)∈E i) then z else 0 := by
  rw [pairedCoordinateMembershipMask_product]
  by_cases hc : C <;>
    by_cases hm : (∀i,x (σ.symm i)∈E i) ∧ (∀i,x (ρ.symm i)∈E i) <;>
    simp [hc,hm]

theorem sourceMaskedRetainedPairAt_membership {k A : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (E : SurvivingPrimeIndex k j (sourceWidth cfg m)→Finset (PrimeUpTo A))
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (q r : PrimeUpTo A)
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    let σr := copiedSurvivingPermutation k j (sourceWidth cfg m) σ
    let ρr := copiedSurvivingPermutation k j (sourceWidth cfg m) ρ
    let x := twoPrimeSample p L S q r
    sourceMaskedRetainedPairAt cfg m j hj σ ρ χ a ζ
      (pairedCoordinateMembershipMask E σr ρr) p L S q r P s t u =
      if Pairwise (fun i v=>(x i).val.Coprime (x v).val) ∧
          (∀i,x (σr.symm i)∈E i) ∧ (∀i,x (ρr.symm i)∈E i)
        then sourceRetainedPairAt cfg m j hj σ ρ χ a ζ p L S q r P s t u else 0 := by
  exact pairedCoordinateMembershipMask_guard E
    (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
    (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ)
    (twoPrimeSample p L S q r)
    (sourceRetainedPairAt cfg m j hj σ ρ χ a ζ p L S q r P s t u) _

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
