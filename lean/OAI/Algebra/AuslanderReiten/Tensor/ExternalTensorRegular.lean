import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorModule

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def regularEquiv : moduleObject k A B A B ≃ₗ[A ⊗[k] B] (A ⊗[k] B) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    let w : A ⊗[k] B := z
    change representation k A B A B a w = a * w
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
    | tmul a b =>
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, mul_add, hx, hy]
      | tmul x y =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl

@[simp] theorem regularEquiv_apply (x : moduleObject k A B A B) :
    regularEquiv k A B x = (x : A ⊗[k] B) := rfl

end ArExplicit.ExternalTensor

end

end OAI
