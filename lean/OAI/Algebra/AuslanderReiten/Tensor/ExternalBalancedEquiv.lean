import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedCore

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open scoped TensorProduct
universe u
variable {k A B E V F G X Y : Type u} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  [AddCommGroup E] [AddCommGroup V] [AddCommGroup F] [AddCommGroup G]
  [AddCommGroup X] [AddCommGroup Y]
  [Module k E] [Module k V] [Module k F] [Module k G] [Module k X] [Module k Y]
  [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V]
  [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y]

variable (e : E ≃ₗ[k] F ⊗[k] G) (v : V ≃ₗ[k] X ⊗[k] Y)
local notation "Sbal" => BalancedTensor k (A ⊗[k] B) E V
local notation "Lbal" => BalancedTensor k A F X
local notation "Rbal" => BalancedTensor k B G Y

variable
  (he : ∀ (a : A) (b : B) (f : F) (g : G),
    MulOpposite.op (a ⊗ₜ[k] b) • e.symm (f ⊗ₜ[k] g) =
      e.symm ((MulOpposite.op a • f) ⊗ₜ[k] (MulOpposite.op b • g)))
  (hv : ∀ (a : A) (b : B) (x : X) (y : Y),
    (a ⊗ₜ[k] b) • v.symm (x ⊗ₜ[k] y) = v.symm ((a • x) ⊗ₜ[k] (b • y)))

include he hv

theorem inverse_forward (z : Sbal) :
    inverse (A := A) (B := B) e v he hv (forward e v he hv z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    obtain ⟨z, rfl⟩ := e.symm.surjective z
    obtain ⟨w, rfl⟩ := v.symm.surjective w
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, hz, hz']
    | tmul f g =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, hw, hw']
      | tmul x y => rw [forward_pure, inverse_pure]

theorem forward_inverse (z : Lbal ⊗[k] Rbal) :
    forward (A := A) (B := B) e v he hv (inverse e v he hv z) = z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [TensorProduct.add_tmul, map_add, hz, hz']
    | tmul f x =>
      induction w using BalancedTensor.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
      | tmul g y => rw [inverse_pure, forward_pure]

def equiv : Sbal ≃ₗ[k] Lbal ⊗[k] Rbal where
  __ := forward e v he hv
  invFun := inverse e v he hv
  left_inv := inverse_forward e v he hv
  right_inv := forward_inverse e v he hv

@[simp] theorem equiv_pure (f : F) (g : G) (x : X) (y : Y) :
    equiv e v he hv (BalancedTensor.tmul (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y))) =
      BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y :=
  forward_pure e v he hv f g x y

end ArExplicit.ExternalBalanced

end

end OAI
