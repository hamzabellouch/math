import OAI.Algebra.AuslanderReiten.Resolutions.SimpleCoverClasses
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverCanonical
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomPositive
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEvaluatedBase

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q

def firstCoverCocycle : (simpleOrdinaryResolution q).complex.X 3 ⟶ (X₀).carrier :=
  ModuleCat.ofHom (X := (simpleOrdinaryResolution q).complex.X 3) (Y := (X₀).carrier) ((firstCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3))
def secondCoverCocycle : (simpleOrdinaryResolution q).complex.X 3 ⟶ (X₀).carrier :=
  ModuleCat.ofHom (X := (simpleOrdinaryResolution q).complex.X 3) (Y := (X₀).carrier) ((secondCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3))

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem firstCoverCocycle_closed :
    (simpleOrdinaryResolution q).complex.d 4 3 ≫ firstCoverCocycle q = 0 := by
  apply ModuleCat.hom_ext
  change ((firstCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)).comp
    (TwoCone.evaluatedBaseDifferential D₀ hf₀ X₀ 3) = 0
  rw [LinearMap.comp_assoc, TwoCone.evaluatedBaseQuotient_comp_d_zero, LinearMap.comp_zero]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem secondCoverCocycle_closed :
    (simpleOrdinaryResolution q).complex.d 4 3 ≫ secondCoverCocycle q = 0 := by
  apply ModuleCat.hom_ext
  change ((secondCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)).comp
    (TwoCone.evaluatedBaseDifferential D₀ hf₀ X₀ 3) = 0
  rw [LinearMap.comp_assoc, TwoCone.evaluatedBaseQuotient_comp_d_zero, LinearMap.comp_zero]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem firstCoverClass_ext (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q) =
      (Ext.mk₀ (evaluatedBaseZeroEquiv q).toModuleIso.inv).comp
        ((simpleOrdinaryResolution q).extMk (firstCoverCocycle q) 4 rfl
          (firstCoverCocycle_closed q))
        (zero_add _) := by
  have h := TwoCone.evaluatedCover_ext_canonical (k := k) (R := R₀) D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) τ₀ X₀
    (evaluatedBaseZeroEquiv q).symm.toLinearMap 2 (firstCubicBack q)
  exact h

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem secondCoverClass_ext (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q) =
      (Ext.mk₀ (evaluatedBaseZeroEquiv q).toModuleIso.inv).comp
        ((simpleOrdinaryResolution q).extMk (secondCoverCocycle q) 4 rfl
          (secondCoverCocycle_closed q))
        (zero_add _) := by
  have h := TwoCone.evaluatedCover_ext_canonical (k := k) (R := R₀) D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) τ₀ X₀
    (evaluatedBaseZeroEquiv q).symm.toLinearMap 2 (secondCubicBack q)
  exact h

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem firstCoverCocycle_eq :
    firstCoverCocycle q = ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0) ≫
      (simpleOrdinaryResolution q).π.f 0 ≫ (evaluatedBaseZeroEquiv q).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  change (evaluatedBaseZeroEquiv q).toLinearMap.comp
    ((FiniteLeftModule.evaluationMap X₀ (TwoCone.firstCokernelMap D₀ 0)).comp
      (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)) =
    (evaluatedBaseZeroEquiv q).toLinearMap.comp
      ((TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 0).comp
        (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0))
  rw [TwoCone.evaluatedFirstBaseMap_quotient]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem secondCoverCocycle_eq :
    secondCoverCocycle q = ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0) ≫
      (simpleOrdinaryResolution q).π.f 0 ≫ (evaluatedBaseZeroEquiv q).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  change (evaluatedBaseZeroEquiv q).toLinearMap.comp
    ((FiniteLeftModule.evaluationMap X₀ (TwoCone.secondCokernelMap D₀ 0)).comp
      (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)) =
    (evaluatedBaseZeroEquiv q).toLinearMap.comp
      ((TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 0).comp
        (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0))
  rw [TwoCone.evaluatedSecondBaseMap_quotient]

end ArExplicit.T

end

end OAI
