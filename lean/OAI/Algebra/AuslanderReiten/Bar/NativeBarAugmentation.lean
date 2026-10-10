import OAI.Algebra.AuslanderReiten.Bar.NativeBarEvaluation
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNative

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

def canonicalCoefficientAugmentation :
    (canonicalCoefficientComplex k R M).X 0 ⟶ ModuleCat.of R M := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (nativeResolution k R M).π.f 0

theorem coefficientScalarIso_augmentation :
    (coefficientScalarIso k R M).hom.f 0 ≫ (nativeResolution k R M).π.f 0 =
      canonicalCoefficientAugmentation k R M := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

end ArExplicit.ModuleBar

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
private theorem compose_augmentation {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (d : D ⟶ E)
    (f : B ⟶ E) (u : A ⟶ F) (v : F ⟶ E)
    (hb : b ≫ d = f) (ha : a ≫ f = u ≫ v) :
    (a ≫ b) ≫ d = u ≫ v := by
  rw [Category.assoc, hb, ha]
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def nativeEndpointObject : ModuleCat.{u} R := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (EnvelopingBimodule.evaluationFunctor k R (ModuleCat.of R M)).obj
    (AbsoluteBar.moduleObject k R 0)

def nativeEndpointIso :
    nativeEndpointObject k R M ≅ ModuleCat.of R M := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (canonicalEquiv k R (ModuleCat.of R M) 0).toModuleIso

def nativeEvaluatedAugmentation :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X 0 ⟶
      nativeEndpointObject k R M := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (EnvelopingBimodule.evaluationFunctor k R (ModuleCat.of R M)).map
    ((AbsoluteBar.resolution k R).π.f 0)

omit [Module k M] [IsScalarTower k R M] in
theorem canonicalComplexIso_augmentation :
    nativeEvaluatedAugmentation k R M ≫ (nativeEndpointIso k R M).hom =
      (canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        ModuleBar.canonicalCoefficientAugmentation k R M := by
  let : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact canonicalDifferentialSquare k R (ModuleCat.of R M) 0

theorem nativeComplexIso_augmentation :
    (nativeComplexIso k R M).hom.f 0 ≫ (ModuleBar.nativeResolution k R M).π.f 0 =
      nativeEvaluatedAugmentation k R M ≫ (nativeEndpointIso k R M).hom := by
  exact compose_augmentation
    ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0)
    ((ModuleBar.coefficientScalarIso k R M).hom.f 0)
    ((ModuleBar.nativeResolution k R M).π.f 0)
    (ModuleBar.canonicalCoefficientAugmentation k R M)
    (nativeEvaluatedAugmentation k R M) (nativeEndpointIso k R M).hom
    (ModuleBar.coefficientScalarIso_augmentation k R M)
    (canonicalComplexIso_augmentation k R M).symm

end ArExplicit.BarBalanced

end

end OAI
