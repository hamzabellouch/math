import OAI.Algebra.AuslanderReiten.Bar.BarBimodule
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def baseEquiv : moduleObject k R 1 ≃ₗ[Enveloping k R] Enveloping k R where
  __ := (TensorProduct.congr (LinearEquiv.refl k R) (MulOpposite.opLinearEquiv k)).toAddEquiv
  map_smul' a x := by
    let y : R ⊗[k] R := x
    change (TensorProduct.congr (LinearEquiv.refl k R) (MulOpposite.opLinearEquiv k))
      ((representation k R 1 a) y) =
      a * (TensorProduct.congr (LinearEquiv.refl k R) (MulOpposite.opLinearEquiv k)) y
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy, mul_add]
      | tmul x y =>
        change (a * x) ⊗ₜ[k] MulOpposite.op (y * MulOpposite.unop b) =
          (a ⊗ₜ[k] b) * (x ⊗ₜ[k] MulOpposite.op y)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl

def rotateLinear (n : ℕ) : object k R (n + 2) ≃ₗ[k] (object k R (n + 1) ⊗[k] R) :=
  (TensorProduct.assoc k R R (object k R n)).symm.trans
    (TensorProduct.rightComm k R R (object k R n))

@[simp] theorem rotateLinear_tmul (n : ℕ) (a b : R) (x : object k R n) :
    rotateLinear k R n (a ⊗ₜ[k] (b ⊗ₜ[k] x)) = (a ⊗ₜ[k] x) ⊗ₜ[k] b := rfl

def rotateEquiv (n : ℕ) : moduleObject k R (n + 2) ≃ₗ[Enveloping k R]
    (moduleObject k R (n + 1) ⊗[k] R) where
  __ := (rotateLinear k R n).toAddEquiv
  map_smul' a x := by
    let y : object k R (n + 2) := x
    change rotateLinear k R n ((representation k R (n + 2) a) y) =
      ((representation k R (n + 1) a).rTensor R) (rotateLinear k R n y)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.rTensor_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        induction y using TensorProduct.inductionOn with
        | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
        | tmul y z =>
          change ((a * x) ⊗ₜ[k] right k R n b z) ⊗ₜ[k] y =
            ((representation k R (n + 1) (a ⊗ₜ[k] b)) (x ⊗ₜ[k] z)) ⊗ₜ[k] y
          rfl

theorem free (n : ℕ) : Module.Free (Enveloping k R) (moduleObject k R (n + 1)) := by
  induction n with
  | zero => exact Module.Free.of_equiv (baseEquiv k R).symm
  | succ n ih =>
    let := ih
    exact Module.Free.of_equiv (rotateEquiv k R n).symm

theorem projective (n : ℕ) : Module.Projective (Enveloping k R) (moduleObject k R (n + 1)) := by
  let := free k R n
  infer_instance

theorem finiteBase [Module.Finite k R] (n : ℕ) : Module.Finite k (object k R n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let := ih
    change Module.Finite k (R ⊗[k] object k R n)
    infer_instance

theorem finite [Module.Finite k R] (n : ℕ) :
    Module.Finite (Enveloping k R) (moduleObject k R (n + 1)) := by
  let : Module.Finite k (moduleObject k R (n + 1)) := finiteBase k R (n + 1)
  exact Module.Finite.of_restrictScalars_finite k (Enveloping k R) _

end ArExplicit.AbsoluteBar

end

end OAI
