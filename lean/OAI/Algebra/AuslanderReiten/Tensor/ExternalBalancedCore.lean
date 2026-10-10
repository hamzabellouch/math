import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorDoubleLift
import Mathlib.RingTheory.TensorProduct.Basic

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

def rawForward : (E ⊗[k] V) →ₗ[k] Lbal ⊗[k] Rbal :=
  (TensorProduct.map (balancingRelations k A F X).mkQ
    (balancingRelations k B G Y).mkQ).comp
    ((TensorProduct.tensorTensorTensorComm k F G X Y).toLinearMap.comp
      (TensorProduct.map e.toLinearMap v.toLinearMap))

def forwardPair : E →ₗ[k] V →ₗ[k] Lbal ⊗[k] Rbal := TensorProduct.curry (rawForward (A := A) (B := B) e v)

omit [Algebra k A] [Algebra k B] [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V] in
@[simp] theorem forwardPair_pure (f : F) (g : G) (x : X) (y : Y) :
    forwardPair (A := A) (B := B) e v (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y)) =
      BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y := by
  simp [forwardPair, rawForward, BalancedTensor.tmul]

variable
  (he : ∀ (a : A) (b : B) (f : F) (g : G),
    MulOpposite.op (a ⊗ₜ[k] b) • e.symm (f ⊗ₜ[k] g) =
      e.symm ((MulOpposite.op a • f) ⊗ₜ[k] (MulOpposite.op b • g)))
  (hv : ∀ (a : A) (b : B) (x : X) (y : Y),
    (a ⊗ₜ[k] b) • v.symm (x ⊗ₜ[k] y) = v.symm ((a • x) ⊗ₜ[k] (b • y)))

include he hv

 theorem forwardPair_balanced (z : E) (r : A ⊗[k] B) (w : V) :
    forwardPair (A := A) (B := B) e v (MulOpposite.op r • z) w = forwardPair (A := A) (B := B) e v z (r • w) := by
  obtain ⟨z, rfl⟩ := e.symm.surjective z
  obtain ⟨w, rfl⟩ := v.symm.surjective w
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [MulOpposite.op_add, add_smul, map_add, LinearMap.add_apply, hr, hs]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, smul_add, LinearMap.add_apply, hz, hz']
    | tmul f g =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, smul_add, hw, hw']
      | tmul x y => rw [he, hv, forwardPair_pure, forwardPair_pure,
          BalancedTensor.balance, BalancedTensor.balance]

def forward : Sbal →ₗ[k] Lbal ⊗[k] Rbal :=
  BalancedTensor.lift (forwardPair (A := A) (B := B) e v) (forwardPair_balanced (A := A) (B := B) e v he hv)

@[simp] theorem forward_pure (f : F) (g : G) (x : X) (y : Y) :
    forward (A := A) (B := B) e v he hv (BalancedTensor.tmul (R := A ⊗[k] B) (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y))) =
      BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y :=
  forwardPair_pure (A := A) (B := B) e v f g x y

def rawInverse : ((F ⊗[k] X) ⊗[k] (G ⊗[k] Y)) →ₗ[k] Sbal :=
  (TensorProduct.lift (BalancedTensor.mk (k := k) (R := A ⊗[k] B))).comp
    ((TensorProduct.map e.symm.toLinearMap v.symm.toLinearMap).comp
      (TensorProduct.tensorTensorTensorComm k F X G Y).toLinearMap)

omit he hv [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y] in
@[simp] theorem rawInverse_pure (f : F) (x : X) (g : G) (y : Y) :
    rawInverse (A := A) (B := B) e v ((f ⊗ₜ[k] x) ⊗ₜ[k] (g ⊗ₜ[k] y)) =
      BalancedTensor.tmul (R := A ⊗[k] B) (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y)) := rfl

 theorem inverse_balanced_left (f : F) (a : A) (x : X) (g : G) (y : Y) :
    BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) (MulOpposite.op a • f) x g y =
      BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) f (a • x) g y := by
  simpa only [BalancedTensor.curryFour_apply, rawInverse_pure, he, hv,
    MulOpposite.op_one, one_smul] using
    (BalancedTensor.balance (k := k) (R := A ⊗[k] B)
      (e.symm (f ⊗ₜ[k] g)) (a ⊗ₜ[k] (1 : B)) (v.symm (x ⊗ₜ[k] y)))

 theorem inverse_balanced_right (f : F) (x : X) (g : G) (b : B) (y : Y) :
    BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) f x (MulOpposite.op b • g) y =
      BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) f x g (b • y) := by
  simpa only [BalancedTensor.curryFour_apply, rawInverse_pure, he, hv,
    MulOpposite.op_one, one_smul] using
    (BalancedTensor.balance (k := k) (R := A ⊗[k] B)
      (e.symm (f ⊗ₜ[k] g)) ((1 : A) ⊗ₜ[k] b) (v.symm (x ⊗ₜ[k] y)))

def inverse : (Lbal ⊗[k] Rbal) →ₗ[k] Sbal :=
  TensorProduct.lift (BalancedTensor.doubleLift (BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v))
    (inverse_balanced_left (A := A) (B := B) e v he hv) (inverse_balanced_right (A := A) (B := B) e v he hv))

@[simp] theorem inverse_pure (f : F) (x : X) (g : G) (y : Y) :
    inverse (A := A) (B := B) e v he hv (BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y) =
      BalancedTensor.tmul (R := A ⊗[k] B) (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y)) := rfl

end ArExplicit.ExternalBalanced

end

end OAI
