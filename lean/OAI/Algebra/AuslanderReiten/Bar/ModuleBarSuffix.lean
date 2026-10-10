import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCochain

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def suffixComparison (p : AbsoluteBar.Cochain3 k R) : (n : ℕ) → object k R M (n + 3) →ₗ[k] object k R M n
  | 0 => suffix3 k R M p
  | n + 1 => (suffixComparison p n).lTensor R

@[simp] theorem suffixComparison_succ_tmul (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (a : R) (x : object k R M (n + 3)) :
    suffixComparison k R M p (n + 1) (a ⊗ₜ[k] x) = a ⊗ₜ[k] suffixComparison k R M p n x := rfl

theorem suffixComparison_left (p : AbsoluteBar.Cochain3 k R) (n : ℕ) (a : R)
    (x : object k R M (n + 4)) :
    suffixComparison k R M p (n + 1) (left k R M (n + 4) a x) =
      left k R M (n + 1) a (suffixComparison k R M p (n + 1) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => rfl

def suffixComparisonMap (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    moduleObject k R M (n + 4) →ₗ[R] moduleObject k R M (n + 1) where
  toAddHom := (suffixComparison k R M p (n + 1)).toAddHom
  map_smul' a x := suffixComparison_left k R M p n a x

variable [CharP k 2]

private theorem double_zero {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

theorem suffixComparison_boundary_zero (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    (boundary k R M 0).comp (suffixComparison k R M p 1) =
      (suffixComparison k R M p 0).comp (boundary k R M 3) := by
  ext a b c d e
  change a • (p b c d • e) = suffix3 k R M p
    (boundary k R M 3 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))))
  have h := congrArg (fun x : R => x • e) (hp a b c d)
  simp only [add_smul, zero_smul, mul_smul] at h
  simp only [boundary_succ_tmul k R M 2, boundary_succ_tmul k R M 1,
    boundary_succ_tmul k R M 0, boundary_zero_tmul k R M,
    left_tmul k R M 2, left_tmul k R M 1, left_tmul k R M 0,
    TensorProduct.tmul_add, map_add, suffix3_tmul k R M p]
  have h' : a • (p b c d • e) +
      (p (a * b) c d • e + (p a (b * c) d • e +
        (p a b (c * d) • e + p a b c • (d • e)))) = 0 := by
    simpa only [add_assoc] using h
  have hz := double_zero k (a • (p b c d • e))
  have hh := congrArg (fun x : M => a • (p b c d • e) + x) h'
  simpa only [← add_assoc, hz, zero_add, add_zero] using hh.symm

theorem suffixComparison_boundary (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) (n : ℕ)
    (x : object k R M (n + 4)) :
    boundary k R M n (suffixComparison k R M p (n + 1) x) =
      suffixComparison k R M p n (boundary k R M (n + 3) x) := by
  induction n with
  | zero => exact LinearMap.congr_fun (suffixComparison_boundary_zero k R M p hp) x
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      change boundary k R M (n + 1) (a ⊗ₜ[k] suffixComparison k R M p (n + 1) x) =
        suffixComparison k R M p (n + 1) (boundary k R M (n + 4) (a ⊗ₜ[k] x))
      rw [boundary_succ_tmul k R M n, boundary_succ_tmul k R M (n + 3), map_add,
        suffixComparison_left k R M p n, suffixComparison_succ_tmul, ih]

omit [CharP k 2] in

theorem suffixComparison_augmentation (p : AbsoluteBar.Cochain3 k R) :
    (differential k R M 0).comp (suffixComparisonMap k R M p 0) = cochain3 k R M p := by
  apply LinearMap.ext
  intro x
  change boundary k R M 0 (suffixComparison k R M p 1 x) = cochain3Linear k R M p x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

end ArExplicit.ModuleBar

end

end OAI
