import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorHom
import OAI.Algebra.AuslanderReiten.HomComplex.NativeHomExtAction
import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtConjugate

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

local instance tensorRestrictionEquivalence :
    (ExternalTensor.tensorRestriction k R S h j).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Algebra.TensorProduct.congr h j).toRingEquiv

def nativeTensorTransportResolutionHom :
    ProjectiveResolution.Hom
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (ResolutionProducts.mapResolution (ExternalTensor.tensorRestriction k R S h j)
        (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N)))
      (nativeTensorEndpointIso k R S M N h j e f he hf).hom where
  hom := nativeTensorTransport k R S M N h j e f he hf
  hom_f_zero_comp_π_f_zero := by
    erw [ResolutionProducts.mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact nativeTensorTransport_augmentation k R S M N h j e f he hf

theorem nativeTensorTwist_eq_exactFunctor (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorTwist k R S M N h j e f he hf n x =
      ((Ext.mk₀ (nativeTensorEndpointIso k R S M N h j e f he hf).hom).comp
        (x.mapExactFunctor (ExternalTensor.tensorRestriction k R S h j)) (zero_add n)).comp
          (Ext.mk₀ (nativeTensorEndpointIso k R S M N h j e f he hf).inv) (add_zero n) := by
  let P := ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N)
  let H := nativeTensorHomTransport k R S M N h j e f he hf
  let E := nativeTensorEndpointIso k R S M N h j e f he hf
  let φ := nativeTensorTransportResolutionHom k R S M N h j e f he hf
  have hcomparison := nativeTensorHomTransport_apply k R S M N h j e f he hf
  let := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  let := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  let U := ExternalTensor.moduleObject k R S (ModuleCat.of R M) (ModuleCat.of S N)
  let : AddCommGroup U := U.isAddCommGroup
  let : Module (R ⊗[k] S) U := U.isModule
  let : Module k U := ExternalTensor.baseModule k R S (ModuleCat.of R M) (ModuleCat.of S N)
  let : IsScalarTower k (R ⊗[k] S) U :=
    ExternalTensor.tower k R S (ModuleCat.of R M) (ModuleCat.of S N)
  have ht := ExternalTensor.nativeHomEndExt_eq_exactFunctor k (R ⊗[k] S)
    U (addY := U.isAddCommGroup) (modY := U.isModule)
    (baseY := ExternalTensor.baseModule k R S (ModuleCat.of R M) (ModuleCat.of S N))
    (towerY := ExternalTensor.tower k R S (ModuleCat.of R M) (ModuleCat.of S N))
    P H (ExternalTensor.tensorRestriction k R S h j) E φ hcomparison n x
  exact ht

end ArExplicit.ModuleBar

end

end OAI
