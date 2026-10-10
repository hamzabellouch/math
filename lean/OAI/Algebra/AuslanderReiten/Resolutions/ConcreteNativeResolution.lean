import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteNativeAugmentation
import OAI.Algebra.AuslanderReiten.Ext.ExternalNativeRegularAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
private theorem augmentation_compose {C : Type*} [Category C]
    {P Q R S U V W : C} (a : P ⟶ Q) (b : Q ⟶ R) (p : R ⟶ S)
    (f : Q ⟶ U) (g : U ⟶ S) (u : P ⟶ V) (v : V ⟶ U)
    (z : P ⟶ W) (w : W ⟶ S)
    (hb : b ≫ p = f ≫ g) (ha : a ≫ f = u ≫ v) (hc : u ≫ (v ≫ g) = z ≫ w) :
    (a ≫ b) ≫ p = z ≫ w := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hc]

universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "S" => Resolution.Simple q
local notation "X" => A.simpleFiniteModule q
local instance concreteNativeResolutionBaseModule : Module k (canonicalTensorSimple q) :=
  moduleCatBaseModule (k := k) (R := A₀) (canonicalTensorSimple q)
local instance concreteNativeResolutionBaseTower : IsScalarTower k A₀ (canonicalTensorSimple q) :=
  moduleCatBaseTower (k := k) (R := A₀) (canonicalTensorSimple q)

def simpleNativeTensorResolution : ProjectiveResolution (canonicalTensorSimple q) :=
  ExternalTensor.projectiveResolution k T₀ T₀ (ModuleBar.nativeResolution k T₀ S)
    (ModuleBar.nativeResolution k T₀ S)

theorem simpleNativeBarIso_augmentation :
    (simpleNativeBarIso q).hom.f 0 ≫ (simpleNativeTensorResolution q).π.f 0 =
      (simpleOrdinaryResolution q).π.f 0 ≫
        (evaluatedBaseZeroEquiv q).toModuleIso.hom ≫ (nativeToCanonicalSimple q).hom := by
  have hbar := ExternalBalanced.nativeTotalBarIso_regularAugmentation k T₀ T₀ S S
  have hcoef := (EnvelopingBimodule.evaluationCoefficientIso k A₀
    (nativeToCanonicalSimple q)).hom.naturality (bimoduleAugmentation q)
  rw [simpleNativeBarIso_hom_f]
  erw [simpleOrdinaryBarIso_f, Category.id_comp]
  exact augmentation_compose
    ((simpleCoefficientComplexIso q).hom.f 0)
    ((ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f 0)
    ((simpleNativeTensorResolution q).π.f 0)
    ((EnvelopingBimodule.evaluationFunctor k A₀ (canonicalTensorSimple q)).map (bimoduleAugmentation q))
    (BarBalanced.nativeEndpointIso k A₀ (canonicalTensorSimple q)).hom
    ((EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier).map (bimoduleAugmentation q))
    ((EnvelopingBimodule.evaluationCoefficientIso k A₀ (nativeToCanonicalSimple q)).hom.app
      (AbsoluteBar.moduleObject k A₀ 0))
    ((simpleOrdinaryResolution q).π.f 0)
    ((evaluatedBaseZeroEquiv q).toModuleIso.hom ≫ (nativeToCanonicalSimple q).hom)
    hbar hcoef.symm (simpleBaseAugmentation q)

def simpleNativeResolutionHom : ProjectiveResolution.Hom (simpleOrdinaryResolution q)
    (simpleNativeTensorResolution q)
    ((evaluatedBaseZeroEquiv q).toModuleIso.hom ≫ (nativeToCanonicalSimple q).hom) where
  hom := (simpleNativeBarIso q).hom
  hom_f_zero_comp_π_f_zero := simpleNativeBarIso_augmentation q

end ArExplicit.T

end

end OAI
