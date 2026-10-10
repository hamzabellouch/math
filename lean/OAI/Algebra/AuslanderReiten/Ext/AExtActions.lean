import OAI.Algebra.AuslanderReiten.Ext.AExtPolynomial
import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethActions
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorClass
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCubic
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]

abbrev aFactorResolution := ModuleBar.nativeResolution k T (Simple q)
local instance aFactorFinite (i : ℕ) : Module.Finite T ((aFactorResolution q).complex.X i) :=
  ModuleBar.nativeResolution_finite k T (Simple q) i

abbrev aFactorCubic := ModuleBar.nativeCubicMap k T (Simple q) (CocycleData.p q)
abbrev aFactorCubic_comm := ModuleBar.nativeCubicMap_comm k T (Simple q)
  (CocycleData.p q) (CocycleData.p_isCocycle3 q)

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
  [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))] in
theorem aFactorExtClass :
    ModuleBar.extClass3 k T (Simple q) (CocycleData.p q) (CocycleData.p_isCocycle3 q) =
      tExplicitP q := rfl

abbrev aCanonicalFirst :=
  ModuleBar.nativeTensorFirst k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

abbrev aCanonicalSecond :=
  ModuleBar.nativeTensorSecond k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

abbrev aFirst :=
  ModuleBar.tensorFirst k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

abbrev aSecond :=
  ModuleBar.tensorSecond k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))] in
theorem aFactorCubic_class :
    ResolutionProducts.endExt (aFactorResolution q)
      (ResolutionProducts.natCubicCocycle (k := k) (aFactorResolution q)
        (aFactorCubic q) (aFactorCubic_comm q)) = tExplicitP q :=
  (ModuleBar.nativeCubicMap_class k T (Simple q) (CocycleData.p q)
    (CocycleData.p_isCocycle3 q)).trans (aFactorExtClass q)

theorem aCanonicalFirst_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k T T (Simple q) (Simple q))
      (ExternalTensor.canonicalTensorObject k T T (Simple q) (Simple q)) n) :
    aCanonicalKunnethEquiv q (n+3) ((aCanonicalFirst q).comp x (by omega)) =
      ExternalTensor.coefficientFirst k T T S S S S (tExplicitP q) n
        (aCanonicalKunnethEquiv q n x) := by
  have ht := ModuleBar.nativeTensorFirst_action_of_class k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) n x
  dsimp only [aCanonicalKunnethEquiv, aExtKunnethEquiv, aCanonicalFirst, aCanonicalSecond,
    aFirst, aSecond, tTensorCoefficients, ArExplicit.A.Simple] at ht ⊢
  exact ht

theorem aCanonicalSecond_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k T T (Simple q) (Simple q))
      (ExternalTensor.canonicalTensorObject k T T (Simple q) (Simple q)) n) :
    aCanonicalKunnethEquiv q (n+3) ((aCanonicalSecond q).comp x (by omega)) =
      ExternalTensor.coefficientSecond k T T S S S S (tExplicitP q) n
        (aCanonicalKunnethEquiv q n x) := by
  have ht := ModuleBar.nativeTensorSecond_action_of_class k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) n x
  dsimp only [aCanonicalKunnethEquiv, aExtKunnethEquiv, aCanonicalFirst, aCanonicalSecond,
    aFirst, aSecond, tTensorCoefficients, ArExplicit.A.Simple] at ht ⊢
  exact ht

theorem aFirst_kunneth (n : ℕ) (x : ASelfExt q n) :
    type_of% (ModuleBar.tensorFirst_action_of_class k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) n x) :=
  ModuleBar.tensorFirst_action_of_class k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) n x

theorem aSecond_kunneth (n : ℕ) (x : ASelfExt q n) :
    type_of% (ModuleBar.tensorSecond_action_of_class k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) n x) :=
  ModuleBar.tensorSecond_action_of_class k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) n x

end ArExplicit.Resolution

end

end OAI
