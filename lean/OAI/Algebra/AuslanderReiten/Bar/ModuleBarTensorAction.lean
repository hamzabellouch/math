import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorTwist
import OAI.Algebra.AuslanderReiten.Ext.TensorExtCoefficients

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
variable (α : ∀ n, Ext (ModuleCat.of R M) (ModuleCat.of R M) n →ₗ[k]
  Ext (ModuleCat.of R M) (ModuleCat.of R M) n)
variable (β : ∀ n, Ext (ModuleCat.of S N) (ModuleCat.of S N) n →ₗ[k]
  Ext (ModuleCat.of S N) (ModuleCat.of S N) n)
variable (hα : ∀ n, twistExtAction k R M h e he n = α n)
variable (hβ : ∀ n, twistExtAction k S N j f hf n = β n)
variable (Φ : ∀ n, (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n) →ₗ[k] (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n))
variable (hΦ : ∀ n (x : (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n)) (p : ExternalTensor.Diagonal n), Φ n x p = TensorProduct.map (α p.val.1) (β p.val.2) (x p))
include hα hβ hΦ

theorem nativeTensorTwist_kunneth_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N n (nativeTensorTwist k R S M N h j e f he hf n x) =
      Φ n (nativeTensorKunneth k R S M N n x) := by
  funext p
  rw [hΦ]
  exact nativeTensorTwist_kunneth_of_factors k R S M N h j e f he hf α β hα hβ n x p

theorem tensorTwist_kunneth_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) =
      Φ n (tensorKunneth k R S M N n x) := by
  funext p
  rw [hΦ]
  exact tensorTwist_kunneth_of_factors k R S M N h j e f he hf α β hα hβ n x p

end ArExplicit.ModuleBar

end

end OAI
