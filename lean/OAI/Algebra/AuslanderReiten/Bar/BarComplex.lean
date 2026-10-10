import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.CharP.Two

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev object : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k R
  | n + 1 => ModuleCat.of k (R ⊗[k] object n)

def left : (n : ℕ) → R →ₐ[k] Module.End k (object k R n)
  | 0 => Algebra.lsmul k k R
  | n + 1 => (Module.End.rTensorAlgHom k R (object k R n)).comp (Algebra.lsmul k k R)

def right : (n : ℕ) → Rᵐᵒᵖ →ₐ[k] Module.End k (object k R n)
  | 0 => Algebra.lsmul k k R
  | n + 1 => (Module.End.lTensorAlgHom k (object k R n) R).comp (right n)

@[simp] theorem left_zero (a x : R) : left k R 0 a x = a * x := rfl
@[simp] theorem right_zero (a : Rᵐᵒᵖ) (x : R) : right k R 0 a x = x * MulOpposite.unop a := rfl
@[simp] theorem left_tmul (n : ℕ) (a b : R) (x : object k R n) :
    left k R (n + 1) a (b ⊗ₜ[k] x) = (a * b) ⊗ₜ[k] x := rfl
@[simp] theorem right_tmul (n : ℕ) (a : Rᵐᵒᵖ) (b : R) (x : object k R n) :
    right k R (n + 1) a (b ⊗ₜ[k] x) = b ⊗ₜ[k] right k R n a x := rfl

@[simp] theorem left_one (n : ℕ) (x : object k R n) : left k R n 1 x = x := by
  rw [map_one]
  rfl

theorem left_mul (n : ℕ) (a b : R) (x : object k R n) :
    left k R n (a * b) x = left k R n a (left k R n b x) := by
  rw [map_mul]
  rfl

theorem left_right (n : ℕ) (a : R) (b : Rᵐᵒᵖ) (x : object k R n) :
    left k R n a (right k R n b x) = right k R n b (left k R n a x) := by
  cases n with
  | zero => exact (mul_assoc _ _ _).symm
  | succ n =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c x => rfl

def boundary : (n : ℕ) → object k R (n + 1) →ₗ[k] object k R n
  | 0 => LinearMap.mul' k R
  | n + 1 => TensorProduct.lift (left k R (n + 1)).toLinearMap + (boundary n).lTensor R

@[simp] theorem boundary_zero_tmul (a b : R) : boundary k R 0 (a ⊗ₜ[k] b) = a * b := rfl
@[simp] theorem boundary_succ_tmul (n : ℕ) (a : R) (x : object k R (n + 1)) :
    boundary k R (n + 1) (a ⊗ₜ[k] x) =
      left k R (n + 1) a x + a ⊗ₜ[k] boundary k R n x := rfl

theorem boundary_left (n : ℕ) (a : R) (x : object k R (n + 1)) :
    boundary k R n (left k R (n + 1) a x) = left k R n a (boundary k R n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    cases n with
    | zero => exact mul_assoc _ _ _
    | succ n =>
      rw [left_tmul, boundary_succ_tmul, boundary_succ_tmul, map_add, left_tmul, ← left_mul]

theorem boundary_right (n : ℕ) (a : Rᵐᵒᵖ) (x : object k R (n + 1)) :
    boundary k R n (right k R (n + 1) a x) = right k R n a (boundary k R n x) := by
  induction n with
  | zero =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b c => exact (mul_assoc _ _ _).symm
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      rw [right_tmul, boundary_succ_tmul, boundary_succ_tmul, map_add, right_tmul, ih, left_right]

variable [CharP k 2]

private theorem double_zero {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

theorem boundary_squared (n : ℕ) (x : object k R (n + 2)) :
    boundary k R n (boundary k R (n + 1) x) = 0 := by
  induction n with
  | zero =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_zero_tmul, left_zero]
      exact double_zero k _
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_succ_tmul, ih,
        TensorProduct.tmul_zero, add_zero]
      exact double_zero k _

def contraction (n : ℕ) : object k R n →ₗ[k] object k R (n + 1) :=
  TensorProduct.mk k R (object k R n) 1

theorem contraction_identity (n : ℕ) (x : object k R (n + 1)) :
    boundary k R (n + 1) (contraction k R (n + 1) x) +
      contraction k R n (boundary k R n x) = x := by
  change boundary k R (n + 1) ((1 : R) ⊗ₜ[k] x) +
    (1 : R) ⊗ₜ[k] boundary k R n x = x
  rw [boundary_succ_tmul, left_one, add_assoc, double_zero k, add_zero]

omit [CharP k 2] in

theorem augmentation_contraction (x : R) : boundary k R 0 (contraction k R 0 x) = x := by
  exact one_mul x

theorem boundary_exact (n : ℕ) :
    LinearMap.range (boundary k R (n + 1)) = LinearMap.ker (boundary k R n) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact boundary_squared k R n x
  · intro x hx
    refine ⟨contraction k R (n + 1) x, ?_⟩
    have h := contraction_identity k R n x
    rw [show boundary k R n x = 0 from hx, map_zero, add_zero] at h
    exact h

end ArExplicit.AbsoluteBar

end

end OAI
