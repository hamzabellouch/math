import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open LinearDetection
open scoped TensorProduct
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

lemma comm_mem_tensorFiltration (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) (x : M ⊗[ℚ] N) (hx : x∈additiveTensorFiltration F G W) :
    TensorProduct.comm ℚ M N x∈additiveTensorFiltration G F W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨u,v,x,y,h,hx,hy,rfl⟩
    exact tmul_mem_additiveTensorFiltration G F (by omega) hy hx
  | zero => simpa only [map_zero] using (additiveTensorFiltration G F W).zero_mem
  | add x y hx hy hix hiy => simpa only [map_add] using (additiveTensorFiltration G F W).add_mem hix hiy
  | smul r x hx hix => simpa only [map_smul] using (additiveTensorFiltration G F W).smul_mem r hix

noncomputable def tensorFiltrationComm (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : additiveTensorFiltration F G W ≃ₗ[ℚ] additiveTensorFiltration G F W :=
  { restrict _ _ (TensorProduct.comm ℚ M N).toLinearMap (comm_mem_tensorFiltration F G W) with
    invFun := fun x=>⟨TensorProduct.comm ℚ N M x.val,comm_mem_tensorFiltration G F W x.val x.property⟩
    left_inv := fun x=>by apply Subtype.ext; exact (TensorProduct.comm ℚ M N).symm_apply_apply x.val
    right_inv := fun x=>by apply Subtype.ext; exact (TensorProduct.comm ℚ M N).apply_symm_apply x.val }

noncomputable def tensorGradeComm (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : Grade (additiveTensorFiltration F G W) (additiveTensorFiltration F G (W+1)) →ₗ[ℚ]
      Grade (additiveTensorFiltration G F W) (additiveTensorFiltration G F (W+1)) :=
  map _ _ _ _ (TensorProduct.comm ℚ M N).toLinearMap
    (comm_mem_tensorFiltration F G W) (comm_mem_tensorFiltration F G (W+1))

lemma tensorGradeComm_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) (x : additiveTensorFiltration F G W) :
    tensorGradeComm F G W (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (tensorFiltrationComm F G W x) := rfl

end ElementaryPositivity.LinearFiltration

end
section
namespace ElementaryPositivity

lemma linearMap_span_ext {K M N : Type*} [Semiring K] [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] (s : Set M)
    (f g : Submodule.span K s →ₗ[K] N)
    (h : ∀ x (hx : x∈s),f ⟨x,Submodule.subset_span hx⟩=g ⟨x,Submodule.subset_span hx⟩) : f=g := by
  ext ⟨x,hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => change f 0=g 0; rw [map_zero,map_zero]
  | add x y hx hy hix hiy =>
    change f (⟨x,hx⟩+⟨y,hy⟩)=g (⟨x,hx⟩+⟨y,hy⟩)
    rw [map_add,map_add,hix,hiy]
  | smul r x hx hix =>
    change f (r • ⟨x,hx⟩)=g (r • ⟨x,hx⟩)
    rw [map_smul,map_smul,hix]

end ElementaryPositivity

end

end OAI
