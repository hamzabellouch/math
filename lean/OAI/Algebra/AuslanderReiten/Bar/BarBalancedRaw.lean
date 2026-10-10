import OAI.Algebra.AuslanderReiten.Bar.BarBimodule
import OAI.Algebra.AuslanderReiten.Bar.ModuleBar

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def rawEval : (n : ℕ) → (AbsoluteBar.object k R n ⊗[k] M) →ₗ[k] ModuleBar.object k R M n
  | 0 => TensorProduct.lift (Algebra.lsmul k k M).toLinearMap
  | n+1 => ((rawEval n).lTensor R).comp
      (TensorProduct.assoc k R (AbsoluteBar.object k R n) M).toLinearMap

@[simp] theorem rawEval_zero (a : R) (m : M) :
    rawEval k R M 0 (a ⊗ₜ[k] m) = a • m := rfl

@[simp] theorem rawEval_succ (n : ℕ) (a : R) (x : AbsoluteBar.object k R n) (m : M) :
    rawEval k R M (n+1) ((a ⊗ₜ[k] x) ⊗ₜ[k] m) =
      a ⊗ₜ[k] rawEval k R M n (x ⊗ₜ[k] m) := rfl

theorem rawEval_right (n : ℕ) (a : Rᵐᵒᵖ) (x : AbsoluteBar.object k R n) (m : M) :
    rawEval k R M n ((AbsoluteBar.right k R n a x) ⊗ₜ[k] m) =
      rawEval k R M n (x ⊗ₜ[k] (MulOpposite.unop a • m)) := by
  induction n with
  | zero => exact mul_smul x (MulOpposite.unop a) m
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul b x =>
      rw [AbsoluteBar.right_tmul, rawEval_succ, rawEval_succ, ih]

theorem rawEval_left (n : ℕ) (a : R) (x : AbsoluteBar.object k R n) (m : M) :
    rawEval k R M n ((AbsoluteBar.left k R n a x) ⊗ₜ[k] m) =
      ModuleBar.left k R M n a (rawEval k R M n (x ⊗ₜ[k] m)) := by
  cases n with
  | zero => exact mul_smul a x m
  | succ n =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul b x => rfl

theorem rawEval_boundary (n : ℕ) (x : AbsoluteBar.object k R (n+1)) (m : M) :
    rawEval k R M n ((AbsoluteBar.boundary k R n x) ⊗ₜ[k] m) =
      ModuleBar.boundary k R M n (rawEval k R M (n+1) (x ⊗ₜ[k] m)) := by
  induction n with
  | zero =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul a b => exact mul_smul a b m
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul a x =>
      rw [AbsoluteBar.boundary_succ_tmul k R n, TensorProduct.add_tmul, map_add,
        rawEval_left, rawEval_succ, rawEval_succ, ModuleBar.boundary_succ_tmul k R M n, ih]

end ArExplicit.BarBalanced

end

end OAI
