import OAI.Algebra.AuslanderReiten.Bar.BarCochain

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def suffixComparison (p : Cochain3 k R) : (n : ℕ) → object k R (n + 3) →ₗ[k] object k R n
  | 0 => suffix3 k R p
  | n + 1 => (suffixComparison p n).lTensor R

@[simp] theorem suffixComparison_succ_tmul (p : Cochain3 k R) (n : ℕ)
    (a : R) (x : object k R (n + 3)) :
    suffixComparison k R p (n + 1) (a ⊗ₜ[k] x) = a ⊗ₜ[k] suffixComparison k R p n x := rfl

theorem suffixComparison_left (p : Cochain3 k R) (n : ℕ) (a : R)
    (x : object k R (n + 4)) :
    suffixComparison k R p (n + 1) (left k R (n + 4) a x) =
      left k R (n + 1) a (suffixComparison k R p (n + 1) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => rfl

theorem suffixComparison_right (p : Cochain3 k R) (n : ℕ) (a : Rᵐᵒᵖ)
    (x : object k R (n + 3)) :
    suffixComparison k R p n (right k R (n + 3) a x) =
      right k R n a (suffixComparison k R p n x) := by
  induction n with
  | zero => exact suffix3_right k R p a x
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      change b ⊗ₜ[k] suffixComparison k R p n (right k R (n + 3) a x) =
        b ⊗ₜ[k] right k R n a (suffixComparison k R p n x)
      rw [ih]

def suffixComparisonMap (p : Cochain3 k R) (n : ℕ) :
    moduleObject k R (n + 4) →ₗ[Enveloping k R] moduleObject k R (n + 1) :=
  bimoduleMap k R (suffixComparison k R p (n + 1))
    (suffixComparison_left k R p n) (suffixComparison_right k R p (n + 1))

variable [CharP k 2]

private theorem double_zero {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

theorem suffixComparison_boundary_zero (p : Cochain3 k R) (hp : IsCocycle3 k R p) :
    (boundary k R 0).comp (suffixComparison k R p 1) =
      (suffixComparison k R p 0).comp (boundary k R 3) := by
  ext a b c d e
  change a * (p b c d * e) = suffix3 k R p
    (boundary k R 3 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))))
  have h := congrArg (fun x : R => x * e) (hp a b c d)
  simp only [add_mul, zero_mul, mul_assoc] at h
  simp only [boundary_succ_tmul k R 2, boundary_succ_tmul k R 1,
    boundary_succ_tmul k R 0, boundary_zero_tmul k R,
    left_tmul k R 2, left_tmul k R 1, left_tmul k R 0,
    TensorProduct.tmul_add, map_add, suffix3_tmul k R p]
  have h' : a * (p b c d * e) +
      (p (a * b) c d * e + (p a (b * c) d * e +
        (p a b (c * d) * e + p a b c * (d * e)))) = 0 := by
    simpa only [add_assoc] using h
  have hz := double_zero k (a * (p b c d * e))
  have hh := congrArg (fun x : R => a * (p b c d * e) + x) h'
  simpa only [← add_assoc, hz, zero_add, add_zero] using hh.symm

theorem suffixComparison_boundary (p : Cochain3 k R) (hp : IsCocycle3 k R p) (n : ℕ)
    (x : object k R (n + 4)) :
    boundary k R n (suffixComparison k R p (n + 1) x) =
      suffixComparison k R p n (boundary k R (n + 3) x) := by
  induction n with
  | zero => exact LinearMap.congr_fun (suffixComparison_boundary_zero k R p hp) x
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      change boundary k R (n + 1) (a ⊗ₜ[k] suffixComparison k R p (n + 1) x) =
        suffixComparison k R p (n + 1) (boundary k R (n + 4) (a ⊗ₜ[k] x))
      rw [boundary_succ_tmul k R n, boundary_succ_tmul k R (n + 3), map_add,
        suffixComparison_left k R p n, suffixComparison_succ_tmul, ih]

omit [CharP k 2] in

theorem suffixComparison_augmentation (p : Cochain3 k R) :
    (differential k R 0).comp (suffixComparisonMap k R p 0) = cochain3 k R p := by
  apply LinearMap.ext
  intro x
  change boundary k R 0 (suffixComparison k R p 1 x) = cochain3Linear k R p x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

end ArExplicit.AbsoluteBar

end

end OAI
