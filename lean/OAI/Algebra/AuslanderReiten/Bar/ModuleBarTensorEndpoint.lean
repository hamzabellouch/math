import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExact
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarIso

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
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

local instance endpointRestrictionEquivalence :
    (ExternalTensor.tensorRestriction k R S h j).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Algebra.TensorProduct.congr h j).toRingEquiv

def tensorEndpointIso : ExternalTensor.moduleObject k R S M N ≅
    (ExternalTensor.tensorRestriction k R S h j).obj
      (ExternalTensor.moduleObject k R S M N) :=
  (ExternalTensor.canonicalTensorIso k R S M N).symm ≪≫
    nativeTensorEndpointIso k R S M N h j e f he hf ≪≫
      (ExternalTensor.tensorRestriction k R S h j).mapIso
        (ExternalTensor.canonicalTensorIso k R S M N)

theorem tensorTwist_eq_exactFunctor (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) n) :
    tensorTwist k R S M N h j e f he hf n x =
      ((Ext.mk₀ (tensorEndpointIso k R S M N h j e f he hf).hom).comp
        (x.mapExactFunctor (ExternalTensor.tensorRestriction k R S h j)) (zero_add n)).comp
          (Ext.mk₀ (tensorEndpointIso k R S M N h j e f he hf).inv) (add_zero n) := by
  unfold tensorTwist
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [ExternalTensor.selfExtScalarEquiv_symm_eq_iso,
    nativeTensorTwist_eq_exactFunctor, ExternalTensor.selfExtScalarEquiv_eq_iso]
  exact selfExtIso_conjugated_functor (k := k)
    (ExternalTensor.tensorRestriction k R S h j)
    (ExternalTensor.canonicalTensorIso k R S M N)
    (nativeTensorEndpointIso k R S M N h j e f he hf) n x

end ArExplicit.ModuleBar

end

end OAI
