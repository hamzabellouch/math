import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedEquiv

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open scoped TensorProduct
universe u
variable {k A B E V F G X Y Z : Type u} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  [AddCommGroup E] [AddCommGroup V] [AddCommGroup F] [AddCommGroup G]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module k E] [Module k V] [Module k F] [Module k G] [Module k X] [Module k Y] [Module k Z]
  [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V]
variable (e : E ≃ₗ[k] F ⊗[k] G) (v : V ≃ₗ[k] X ⊗[k] Y)

theorem fourfold_hom_ext (f g : BalancedTensor k (A ⊗[k] B) E V →ₗ[k] Z)
    (h : ∀ a b x y, f (BalancedTensor.tmul (e.symm (a ⊗ₜ[k] b)) (v.symm (x ⊗ₜ[k] y))) =
      g (BalancedTensor.tmul (e.symm (a ⊗ₜ[k] b)) (v.symm (x ⊗ₜ[k] y)))) : f=g := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    obtain ⟨z, rfl⟩ := e.symm.surjective z
    obtain ⟨w, rfl⟩ := v.symm.surjective w
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, hz, hz']
    | tmul a b =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, hw, hw']
      | tmul x y => exact h a b x y

end ArExplicit.ExternalBalanced

end

end OAI
