import OAI.Algebra.AuslanderReiten.Bar.ExternalBarFreeAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

theorem barCyclicCover_tmul (a : A) (b : B) :
    barCyclicCover k A B M N e f (a ⊗ₜ[k] b) =
      canonicalTmul k A B M N (a • e.symm 1) (b • f.symm 1) := by
  change (mapHom k A B (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
    (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f)))
      ((canonicalTensorIso k A B A B).inv (a ⊗ₜ[k] b)) = _
  rw [canonicalTensorIso_inv_tmul]
  rfl

def tensorCyclicCover : (A ⊗[k] B) →ₗ[A ⊗[k] B] moduleObject k A B M N where
  toFun a := a • (show moduleObject k A B M N from e.symm 1 ⊗ₜ[k] f.symm 1)
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

theorem barCyclicCover_eq :
    barCyclicCover k A B M N e f =
      ModuleCat.ofHom (tensorCyclicCover k A B M N e f) ≫
        (canonicalTensorIso k A B M N).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [barCyclicCover_tmul]
    change canonicalTmul k A B M N (a • e.symm 1) (b • f.symm 1) =
      (canonicalTensorIso k A B M N).inv ((a ⊗ₜ[k] b) •
        (show moduleObject k A B M N from e.symm 1 ⊗ₜ[k] f.symm 1))
    change canonicalTmul k A B M N (a • e.symm 1) (b • f.symm 1) =
      (canonicalTensorIso k A B M N).inv ((a • e.symm 1) ⊗ₜ[k] (b • f.symm 1))
    exact (canonicalTensorIso_inv_tmul k A B M N (a • e.symm 1) (b • f.symm 1)).symm

end ArExplicit.ExternalTensor

end

end OAI
