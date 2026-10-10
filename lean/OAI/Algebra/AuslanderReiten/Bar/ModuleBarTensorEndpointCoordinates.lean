import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorEndpoint

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [mM : Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [mN : Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)

omit [CharP k 2] [Module.Finite k R] [Module.Finite k S] in
theorem tensorEndpointIso_apply (x : M ⊗[k] N) :
    (tensorEndpointIso k R S M N h j e f he hf).hom.hom x =
      TensorProduct.map e.toLinearMap f.toLinearMap x := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  cases ExternalTensor.canonicalScalar_eq k S N (mM := mN)
  rfl

end ArExplicit.ModuleBar

end

end OAI
