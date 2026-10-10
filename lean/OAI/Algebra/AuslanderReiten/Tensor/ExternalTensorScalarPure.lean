import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [μ : Module k M] [ν : Module k N] [IsScalarTower k A M] [IsScalarTower k B N]

def canonicalTmul (x : M) (y : N) : canonicalTensorObject k A B M N :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := A) (ModuleCat.of A M)
  letI : Module k N := moduleCatBaseModule (k := k) (R := B) (ModuleCat.of B N)
  x ⊗ₜ[k] y

@[simp] theorem canonicalTensorIso_tmul (x : M) (y : N) :
    (canonicalTensorIso k A B M N).hom (canonicalTmul k A B M N x y) = x ⊗ₜ[k] y := by
  cases canonicalScalar_eq k A M (mM := μ)
  cases canonicalScalar_eq k B N (mM := ν)
  rfl

@[simp] theorem canonicalTensorIso_inv_tmul (x : M) (y : N) :
    (canonicalTensorIso k A B M N).inv (x ⊗ₜ[k] y) = canonicalTmul k A B M N x y := by
  cases canonicalScalar_eq k A M (mM := μ)
  cases canonicalScalar_eq k B N (mM := ν)
  rfl

end ArExplicit.ExternalTensor

end

end OAI
