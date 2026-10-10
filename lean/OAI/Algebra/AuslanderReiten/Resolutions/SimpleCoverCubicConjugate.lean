import OAI.Algebra.AuslanderReiten.Resolutions.ConcreteNativeResolution
import OAI.Algebra.AuslanderReiten.Ext.SimpleCoverExt
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCubicConjugate
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarScalarClass
import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicClasses

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
local notation "T₀" => T k q
local notation "S₀" => Resolution.Simple q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q

private theorem firstCoverConjugateStart :
    type_of% (ModuleBar.resolutionExt_nativeFirst k T₀ T₀ S₀ S₀
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (simpleOrdinaryResolution q)
      (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)) :=
  ModuleBar.resolutionExt_nativeFirst k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (simpleOrdinaryResolution q)
    (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)

private theorem firstCoverConjugateComparison :
    type_of% (firstCoverConjugateStart q (simpleNativeResolutionHom q)) :=
  firstCoverConjugateStart q (simpleNativeResolutionHom q)

private theorem firstCoverConjugateCocycle :
    type_of% (firstCoverConjugateComparison q
      (ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0))
      (firstCoverCocycle q) (firstCoverCocycle_closed q) (firstCoverCocycle_eq q)) :=
  firstCoverConjugateComparison q
    (ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0))
    (firstCoverCocycle q) (firstCoverCocycle_closed q) (firstCoverCocycle_eq q)

private theorem firstCoverConjugateProof :
    type_of% (firstCoverConjugateCocycle q (simpleNativeBarIso_first q 0)) :=
  firstCoverConjugateCocycle q (simpleNativeBarIso_first q 0)

theorem firstCoverCocycle_conjugate : type_of% (firstCoverConjugateProof q) :=
  firstCoverConjugateProof q

private theorem secondCoverConjugateStart :
    type_of% (ModuleBar.resolutionExt_nativeSecond k T₀ T₀ S₀ S₀
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (simpleOrdinaryResolution q)
      (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)) :=
  ModuleBar.resolutionExt_nativeSecond k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (simpleOrdinaryResolution q)
    (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)

private theorem secondCoverConjugateComparison :
    type_of% (secondCoverConjugateStart q (simpleNativeResolutionHom q)) :=
  secondCoverConjugateStart q (simpleNativeResolutionHom q)

private theorem secondCoverConjugateCocycle :
    type_of% (secondCoverConjugateComparison q
      (ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0))
      (secondCoverCocycle q) (secondCoverCocycle_closed q) (secondCoverCocycle_eq q)) :=
  secondCoverConjugateComparison q
    (ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0))
    (secondCoverCocycle q) (secondCoverCocycle_closed q) (secondCoverCocycle_eq q)

private theorem secondCoverConjugateProof :
    type_of% (secondCoverConjugateCocycle q (simpleNativeBarIso_second q 0)) :=
  secondCoverConjugateCocycle q (simpleNativeBarIso_second q 0)

theorem secondCoverCocycle_conjugate : type_of% (secondCoverConjugateProof q) :=
  secondCoverConjugateProof q

theorem firstCoverClass_conjugate (hq1 : 1+q ≠ 0) :
    selfExtIso (k := k) (nativeToCanonicalSimple q) 3
      (A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q)) =
      Resolution.aCanonicalFirst q := by
  rw [firstCoverClass_ext]
  dsimp only [Resolution.aCanonicalFirst]
  exact firstCoverCocycle_conjugate q

theorem secondCoverClass_conjugate (hq1 : 1+q ≠ 0) :
    selfExtIso (k := k) (nativeToCanonicalSimple q) 3
      (A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q)) =
      Resolution.aCanonicalSecond q := by
  rw [secondCoverClass_ext]
  dsimp only [Resolution.aCanonicalSecond]
  exact secondCoverCocycle_conjugate q

theorem firstCoverClass_ext_eq (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q) = Resolution.aFirst q := by
  exact ModuleBar.tensorFirst_eq_of_conjugate k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q))
    (firstCoverClass_conjugate q hq1)

theorem secondCoverClass_ext_eq (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q) = Resolution.aSecond q := by
  exact ModuleBar.tensorSecond_eq_of_conjugate k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q))
    (secondCoverClass_conjugate q hq1)

theorem firstCoverClass_eq (hq1 : 1+q ≠ 0) :
    firstCoverClass q = A.firstFullClass q hq1 := by
  apply (A.fullNonnegativeExtEquiv q hq1 3).injective
  exact (firstCoverClass_ext_eq q hq1).trans
    ((A.fullNonnegativeExtEquiv q hq1 3).apply_symm_apply _).symm

theorem secondCoverClass_eq (hq1 : 1+q ≠ 0) :
    secondCoverClass q = A.secondFullClass q hq1 := by
  apply (A.fullNonnegativeExtEquiv q hq1 3).injective
  exact (secondCoverClass_ext_eq q hq1).trans
    ((A.fullNonnegativeExtEquiv q hq1 3).apply_symm_apply _).symm

end ArExplicit.T

end

end OAI
