import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section
noncomputable section
namespace NuclearUnitization
open scoped TensorProduct

universe u v

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

def tensorInr : A ⊗[ℂ] B →⋆ₙₐ[ℂ] (Unitization ℂ A) ⊗[ℂ] B where
  toFun := TensorProduct.map (Unitization.inrHom ℂ ℂ A) (LinearMap.id : B →ₗ[ℂ] B)
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,add_mul,hx,hy]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add,mul_add,hx,hy]
      | tmul c d => simp
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [star_add,map_add,hx,hy]
    | tmul a b => simp

@[simp] lemma tensorInr_tmul (a : A) (b : B) :
    tensorInr (a ⊗ₜ[ℂ] b)=(Unitization.inr a) ⊗ₜ[ℂ] b := rfl

lemma tensorInr_injective : Function.Injective (tensorInr : A ⊗[ℂ] B → (Unitization ℂ A) ⊗[ℂ] B) := by
  let g := TensorProduct.map (Unitization.sndHom ℂ ℂ A) (LinearMap.id : B →ₗ[ℂ] B)
  have hg (x : A ⊗[ℂ] B) : g (tensorInr x)=x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul a b => simp [g]
  exact Function.LeftInverse.injective hg

lemma tensor_split (z : (Unitization ℂ A) ⊗[ℂ] B) :
    ∃ w : A ⊗[ℂ] B, ∃ b : B, z=tensorInr w+(1 : Unitization ℂ A) ⊗ₜ[ℂ] b := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨w,b,rfl⟩ := hx
    obtain ⟨v,c,rfl⟩ := hy
    exact ⟨w+v,b+c,by simp only [map_add,TensorProduct.tmul_add]; abel⟩
  | tmul a b =>
    refine ⟨a.snd ⊗ₜ[ℂ] b,a.fst • b,?_⟩
    have ha : a=Unitization.inr a.snd+a.fst • (1 : Unitization ℂ A) := by
      ext <;> simp
    nth_rw 1 [ha]
    rw [TensorProduct.add_tmul,TensorProduct.smul_tmul]
    rfl

end NuclearUnitization

end
end

end OAI
