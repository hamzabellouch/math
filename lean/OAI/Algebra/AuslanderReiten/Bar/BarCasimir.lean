import OAI.Algebra.AuslanderReiten.Bar.BarSuffix

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def casimirMap (ξ : object k R 1) : R →ₗ[k] object k R 1 :=
  (left k R 1).toLinearMap.flip ξ

@[simp] theorem casimirMap_apply (ξ : object k R 1) (a : R) :
    casimirMap k R ξ a = left k R 1 a ξ := rfl

theorem casimirMap_left (ξ : object k R 1) (a b : R) :
    casimirMap k R ξ (a * b) = left k R 1 a (casimirMap k R ξ b) :=
  left_mul k R 1 a b ξ

def casimirInsertion (ξ : object k R 1) : (n : ℕ) → object k R n →ₗ[k] object k R (n + 1)
  | 0 => casimirMap k R ξ
  | n + 1 => (casimirInsertion ξ n).lTensor R

@[simp] theorem casimirInsertion_tmul (ξ : object k R 1) (n : ℕ)
    (a : R) (x : object k R n) :
    casimirInsertion k R ξ (n + 1) (a ⊗ₜ[k] x) =
      a ⊗ₜ[k] casimirInsertion k R ξ n x := rfl

theorem casimirInsertion_left (ξ : object k R 1) (n : ℕ) (a : R) (x : object k R n) :
    casimirInsertion k R ξ n (left k R n a x) =
      left k R (n + 1) a (casimirInsertion k R ξ n x) := by
  cases n with
  | zero => exact casimirMap_left k R ξ a x
  | succ n =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x => rfl

theorem casimirInsertion_right (ξ : object k R 1) (h : R ≃ₐ[k] R)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ)
    (n : ℕ) (a : R) (x : object k R n) :
    casimirInsertion k R ξ n (right k R n (MulOpposite.op (h a)) x) =
      right k R (n + 1) (MulOpposite.op a) (casimirInsertion k R ξ n x) := by
  induction n with
  | zero =>
    change left k R 1 (x * h a) ξ = right k R 1 (MulOpposite.op a) (left k R 1 x ξ)
    rw [left_mul, hξ, left_right]
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      change b ⊗ₜ[k] casimirInsertion k R ξ n (right k R n (MulOpposite.op (h a)) x) =
        b ⊗ₜ[k] right k R (n + 1) (MulOpposite.op a) (casimirInsertion k R ξ n x)
      rw [ih]

theorem casimirMap_boundary (ξ : object k R 1) (hξ : boundary k R 0 ξ = 0) (a : R) :
    boundary k R 0 (casimirMap k R ξ a) = 0 := by
  rw [casimirMap_apply, boundary_left, hξ, map_zero]

theorem casimirInsertion_boundary_zero (ξ : object k R 1) (hξ : boundary k R 0 ξ = 0)
    (x : object k R 1) :
    boundary k R 1 (casimirInsertion k R ξ 1 x) =
      casimirMap k R ξ (boundary k R 0 x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    change boundary k R 1 (a ⊗ₜ[k] casimirMap k R ξ b) = casimirMap k R ξ (a * b)
    rw [boundary_succ_tmul, casimirMap_boundary k R ξ hξ, TensorProduct.tmul_zero,
      add_zero, casimirMap_left]

variable [CharP k 2]

private theorem double_zero {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

theorem casimirInsertion_boundary (ξ : object k R 1) (hξ : boundary k R 0 ξ = 0)
    (n : ℕ) (x : object k R (n + 1)) :
    boundary k R (n + 1) (casimirInsertion k R ξ (n + 1) x) +
      casimirInsertion k R ξ n (boundary k R n x) = 0 := by
  induction n with
  | zero =>
    rw [casimirInsertion_boundary_zero k R ξ hξ]
    exact double_zero k _
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add]
      calc
        _ = (boundary k R (n + 1 + 1) (casimirInsertion k R ξ (n + 1 + 1) x) +
          casimirInsertion k R ξ (n + 1) (boundary k R (n + 1) x)) +
          (boundary k R (n + 1 + 1) (casimirInsertion k R ξ (n + 1 + 1) y) +
          casimirInsertion k R ξ (n + 1) (boundary k R (n + 1) y)) := by abel
        _ = 0 := by rw [hx, hy, add_zero]
    | tmul a x =>
      rw [casimirInsertion_tmul, boundary_succ_tmul, boundary_succ_tmul,
        map_add, casimirInsertion_left, casimirInsertion_tmul]
      have hi := congrArg (fun z => a ⊗ₜ[k] z) (ih x)
      rw [TensorProduct.tmul_add, TensorProduct.tmul_zero] at hi
      calc
        _ = (left k R (n + 1 + 1) a (casimirInsertion k R ξ (n + 1) x) +
          left k R (n + 1 + 1) a (casimirInsertion k R ξ (n + 1) x)) +
          (a ⊗ₜ[k] boundary k R (n + 1) (casimirInsertion k R ξ (n + 1) x) +
          a ⊗ₜ[k] casimirInsertion k R ξ n (boundary k R n x)) := by abel
        _ = 0 := by rw [double_zero k, hi, add_zero]

end ArExplicit.AbsoluteBar

end

end OAI
