import OAI.Algebra.AuslanderReiten.Bar.NativeBarEvaluation
import OAI.Algebra.AuslanderReiten.Bar.CanonicalBarPure
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarFreeCoordinate

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

def canonicalCoefficientTensor (a : R) (m : M) : (canonicalCoefficientComplex k R M).X 0 :=
  BarBalanced.coefficientPure k R (ModuleCat.of R M) a m

@[simp] theorem coefficientScalarIso_tmul (a : R) (m : M) :
    (coefficientScalarIso k R M).hom.f 0 (canonicalCoefficientTensor k R M a m) =
      a ⊗ₜ[k] m := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

end ArExplicit.ModuleBar

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def canonicalEvaluatedTensor (a b : R) (m : M) :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X 0 :=
  canonicalPure k R (ModuleCat.of R M) a b m

def nativeFreeEndpoint (e : M ≃ₗ[k] k) :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X 0 ⟶
      ModuleCat.of R R :=
  (nativeComplexIso k R M).hom.f 0 ≫ (ModuleBar.freeCoordinate k R M e).toModuleIso.hom

omit [Module k M] [IsScalarTower k R M] in
theorem canonicalComplexIso_tensor (a b : R) (m : M) :
    type_of% (canonicalComplexIso_pure k R (ModuleCat.of R M) a b m) :=
  canonicalComplexIso_pure k R (ModuleCat.of R M) a b m

theorem nativeComplexIso_component (n : ℕ) :
    (nativeComplexIso k R M).hom.f n =
      (canonicalComplexIso k R (ModuleCat.of R M)).hom.f n ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f n := rfl

theorem nativeFreeEndpoint_component (e : M ≃ₗ[k] k) :
    nativeFreeEndpoint k R M e =
      ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f 0) ≫
          (ModuleBar.freeCoordinate k R M e).toModuleIso.hom := by
  rw [nativeFreeEndpoint, nativeComplexIso_component]

private theorem compValues {R : Type*} [Ring R] {X Y Z : ModuleCat R}
    (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) : (f ≫ g) x = z := by
  rw [ModuleCat.comp_apply, hf, hg]

private theorem nativeScalarValues (a b : R) (m : M) :
    type_of% (compValues ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0)
      ((ModuleBar.coefficientScalarIso k R M).hom.f 0)
      (canonicalComplexIso_tensor k R M a b m)
      (ModuleBar.coefficientScalarIso_tmul k R M a (b • m))) :=
  compValues ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0)
    ((ModuleBar.coefficientScalarIso k R M).hom.f 0)
    (canonicalComplexIso_tensor k R M a b m)
    (ModuleBar.coefficientScalarIso_tmul k R M a (b • m))

private theorem nativeFreeValues (e : M ≃ₗ[k] k) (a b : R) (m : M) :
    type_of% (compValues
      ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f 0)
      (ModuleBar.freeCoordinate k R M e).toModuleIso.hom
      (nativeScalarValues k R M a b m)
      (ModuleBar.freeCoordinate_tmul k R M e a (b • m))) :=
  compValues
      ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f 0)
      (ModuleBar.freeCoordinate k R M e).toModuleIso.hom
      (nativeScalarValues k R M a b m)
      (ModuleBar.freeCoordinate_tmul k R M e a (b • m))

private theorem valueOfEq {R : Type*} [Ring R] {X Y : ModuleCat R}
    {f g : X ⟶ Y} (h : f = g) {x : X} {y : Y} (hv : g x = y) : f x = y := by
  rw [h, hv]

@[simp] theorem nativeFreeEndpoint_tensor (e : M ≃ₗ[k] k) (a b : R) (m : M) :
    type_of% (valueOfEq (nativeFreeEndpoint_component k R M e)
      (nativeFreeValues k R M e a b m)) :=
  valueOfEq (nativeFreeEndpoint_component k R M e) (nativeFreeValues k R M e a b m)

end ArExplicit.BarBalanced

end

end OAI
