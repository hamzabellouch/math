import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section
noncomputable section
namespace Pureness
open scoped TensorProduct CStarAlgebra

variable {A B D E : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [CStarAlgebra E]

def starTensorMap (f : A →⋆ₐ[ℂ] D) (g : B →⋆ₐ[ℂ] E) : A ⊗[ℂ] B →⋆ₐ[ℂ] D ⊗[ℂ] E :=
  { Algebra.TensorProduct.map f.toAlgHom g.toAlgHom with
    map_star' := by
      intro z
      change (Algebra.TensorProduct.map f.toAlgHom g.toAlgHom) (star z)=
        star ((Algebra.TensorProduct.map f.toAlgHom g.toAlgHom) z)
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp only [TensorProduct.star_tmul,Algebra.TensorProduct.map_tmul,
          StarAlgHom.coe_toAlgHom,map_star]
      | add x y hx hy => simp only [star_add,map_add,hx,hy] }
@[simp] lemma starTensorMap_tmul (f : A →⋆ₐ[ℂ] D) (g : B →⋆ₐ[ℂ] E) (a : A) (b : B) :
    starTensorMap f g (a ⊗ₜ[ℂ] b)=f a ⊗ₜ[ℂ] g b := rfl
lemma starTensorMap_injective (f : A →⋆ₐ[ℂ] D) (g : B →⋆ₐ[ℂ] E)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (starTensorMap f g) :=
  TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

def tensorLeft (f : A ⊗[ℂ] B →⋆ₐ[ℂ] D) : A →⋆ₐ[ℂ] D :=
  f.comp { Algebra.TensorProduct.includeLeft with
    map_star' := by
      intro a
      change star a ⊗ₜ[ℂ] (1:B)=star (a ⊗ₜ[ℂ] (1:B))
      rw [TensorProduct.star_tmul,star_one] }
def tensorRight (f : A ⊗[ℂ] B →⋆ₐ[ℂ] D) : B →⋆ₐ[ℂ] D :=
  f.comp { Algebra.TensorProduct.includeRight with
    map_star' := by
      intro b
      change (1:A) ⊗ₜ[ℂ] star b=star ((1:A) ⊗ₜ[ℂ] b)
      rw [TensorProduct.star_tmul,star_one] }
@[simp] lemma tensorLeft_apply (f : A ⊗[ℂ] B →⋆ₐ[ℂ] D) (a : A) :
    tensorLeft f a=f (a ⊗ₜ[ℂ] 1) := rfl
@[simp] lemma tensorRight_apply (f : A ⊗[ℂ] B →⋆ₐ[ℂ] D) (b : B) :
    tensorRight f b=f (1 ⊗ₜ[ℂ] b) := rfl
end Pureness

end
end

end OAI
