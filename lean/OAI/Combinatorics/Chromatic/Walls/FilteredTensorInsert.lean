import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

noncomputable def tensorFiltrationAssoc (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (W : ℤ) :
    additiveTensorFiltration (additiveTensorFiltration F G) H W ≃ₗ[K]
      additiveTensorFiltration F (additiveTensorFiltration G H) W :=
  { toFun := fun x=>⟨TensorProduct.assoc K A B C x.val,assoc_mem_tensorFiltration F G H W x.val x.property⟩
    invFun := fun x=>⟨(TensorProduct.assoc K A B C).symm x.val,unassoc_mem_tensorFiltration F G H W x.val x.property⟩
    left_inv := by intro x; apply Subtype.ext; exact (TensorProduct.assoc K A B C).symm_apply_apply x.val
    right_inv := by intro x; apply Subtype.ext; exact (TensorProduct.assoc K A B C).apply_symm_apply x.val
    map_add' := by intro x y; apply Subtype.ext; exact (TensorProduct.assoc K A B C).map_add x.val y.val
    map_smul' := by intro r x; apply Subtype.ext; exact (TensorProduct.assoc K A B C).map_smul r x.val }

noncomputable def unassocTensorFixedLeft (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (U V : ℤ) (x : F U) :
    additiveTensorFiltration G H V →ₗ[K] additiveTensorFiltration (additiveTensorFiltration F G) H (U+V) :=
  (((TensorProduct.assoc K A B C).symm.toLinearMap.comp (TensorProduct.mk K A (B⊗[K]C) x.val)).comp
    (additiveTensorFiltration G H V).subtype).codRestrict _ (fun y=>
      unassoc_mem_tensorFiltration F G H (U+V) (x.val⊗ₜ[K]y.val)
        (tmul_mem_additiveTensorFiltration F (additiveTensorFiltration G H) (le_refl _) x.property y.property))

end ElementaryPositivity.LinearDetection

end

end OAI
