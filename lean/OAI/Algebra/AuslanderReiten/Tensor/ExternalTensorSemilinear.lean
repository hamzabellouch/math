import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorModule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {M N M' N' : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
variable [Module k M] [Module k N] [Module k M'] [Module k N']
variable [Module A M] [Module B N] [Module A M'] [Module B N']
variable [IsScalarTower k A M] [IsScalarTower k B N]
variable [IsScalarTower k A M'] [IsScalarTower k B N']
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)
variable (e : M →ₗ[k] M') (f : N →ₗ[k] N')
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ b n, f (b • n) = j b • f n)

include he hf in
theorem tensorSemilinear_smul (r : A ⊗[k] B) (x : moduleObject k A B M N) :
    TensorProduct.map e f (r • x) =
      (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom r) •
        (show moduleObject k A B M' N' from TensorProduct.map e f x) := by
  let w : M ⊗[k] N := x
  change TensorProduct.map e f (representation k A B M N r w) =
    representation k A B M' N' (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom r)
      (TensorProduct.map e f w)
  induction r using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m n =>
      change e (a • m) ⊗ₜ[k] f (b • n) = (h a • e m) ⊗ₜ[k] (j b • f n)
      rw [he, hf]

def tensorSemilinear : moduleObject k A B M N →ₗ[A ⊗[k] B]
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom).toRingHom).obj
        (moduleObject k A B M' N') where
  toAddHom := (TensorProduct.map e f).toAddHom
  map_smul' := tensorSemilinear_smul k A B h j e f he hf

@[simp] theorem tensorSemilinear_tmul (m : M) (n : N) :
    tensorSemilinear k A B h j e f he hf (m ⊗ₜ[k] n) = e m ⊗ₜ[k] f n := rfl

def tensorSemilinearEquiv (e : M ≃ₗ[k] M') (f : N ≃ₗ[k] N')
    (he : ∀ a m, e (a • m) = h a • e m)
    (hf : ∀ b n, f (b • n) = j b • f n) :
    moduleObject k A B M N ≃ₗ[A ⊗[k] B]
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom).toRingHom).obj
          (moduleObject k A B M' N') :=
  LinearEquiv.ofBijective (tensorSemilinear k A B h j e.toLinearMap f.toLinearMap he hf)
    (TensorProduct.congr e f).bijective

theorem tensorSemilinearEquiv_symm_apply (e : M ≃ₗ[k] M') (f : N ≃ₗ[k] N')
    (he : ∀ a m, e (a • m) = h a • e m)
    (hf : ∀ b n, f (b • n) = j b • f n)
    (z : moduleObject k A B M' N') :
    (tensorSemilinearEquiv k A B h j e f he hf).symm z =
      (TensorProduct.congr e f).symm z := by
  apply (tensorSemilinearEquiv k A B h j e f he hf).injective
  erw [LinearEquiv.apply_symm_apply]
  exact ((TensorProduct.congr e f).apply_symm_apply z).symm

end ArExplicit.ExternalTensor

end

end OAI
