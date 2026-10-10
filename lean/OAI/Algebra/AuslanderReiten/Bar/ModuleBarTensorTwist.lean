import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNativeTwist
import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethMap

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

def nativeTensorTwist (n : ℕ) :
    Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n →ₗ[k]
    Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n :=
  ExternalTensor.tensorHomEndExt k R S (nativeResolution k R M) (nativeResolution k S N)
    (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf) n

theorem nativeTensorTwist_kunneth (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) (p : ExternalTensor.Diagonal n) :
    nativeTensorKunneth k R S M N n (nativeTensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (twistExtAction k R M h e he p.val.1)
        (twistExtAction k S N j f hf p.val.2)
        (nativeTensorKunneth k R S M N n x p) := by
  unfold nativeTensorKunneth nativeTensorTwist
  have ht := ExternalTensor.extKunnethEquiv_tensorHomEndExt k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf) n x p
  rw [nativeHomTransport_ext, nativeHomTransport_ext] at ht
  exact ht

def tensorTwist (n : ℕ) :
    Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n →ₗ[k]
      Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n :=
  (ExternalTensor.selfExtScalarEquiv k R S M N n).symm.toLinearMap.comp
    ((nativeTensorTwist k R S M N h j e f he hf n).comp
      (ExternalTensor.selfExtScalarEquiv k R S M N n).toLinearMap)

theorem tensorTwist_kunneth (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n)
    (p : ExternalTensor.Diagonal n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (twistExtAction k R M h e he p.val.1)
        (twistExtAction k S N j f hf p.val.2) (tensorKunneth k R S M N n x p) := by
  unfold tensorKunneth tensorTwist
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact nativeTensorTwist_kunneth k R S M N h j e f he hf n _ p

variable (α : ∀ n, Ext (ModuleCat.of R M) (ModuleCat.of R M) n →ₗ[k]
  Ext (ModuleCat.of R M) (ModuleCat.of R M) n)
variable (β : ∀ n, Ext (ModuleCat.of S N) (ModuleCat.of S N) n →ₗ[k]
  Ext (ModuleCat.of S N) (ModuleCat.of S N) n)
variable (hα : ∀ n, twistExtAction k R M h e he n = α n)
variable (hβ : ∀ n, twistExtAction k S N j f hf n = β n)
include hα hβ

theorem nativeTensorTwist_kunneth_of_factors (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) (p : ExternalTensor.Diagonal n) :
    nativeTensorKunneth k R S M N n (nativeTensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (α p.val.1) (β p.val.2) (nativeTensorKunneth k R S M N n x p) := by
  rw [← hα, ← hβ]
  exact nativeTensorTwist_kunneth k R S M N h j e f he hf n x p

theorem tensorTwist_kunneth_of_factors (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n)
    (p : ExternalTensor.Diagonal n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (α p.val.1) (β p.val.2) (tensorKunneth k R S M N n x p) := by
  rw [← hα, ← hβ]
  exact tensorTwist_kunneth k R S M N h j e f he hf n x p

end ArExplicit.ModuleBar

end

end OAI
