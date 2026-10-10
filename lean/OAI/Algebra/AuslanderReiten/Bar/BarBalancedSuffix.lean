import OAI.Algebra.AuslanderReiten.Bar.BarBalancedRaw
import OAI.Algebra.AuslanderReiten.Bar.BarSuffix
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarSuffix

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem rawEval_suffix_zero (p : AbsoluteBar.Cochain3 k R)
    (x : AbsoluteBar.object k R 3) (m : M) :
    rawEval k R M 0 (AbsoluteBar.suffix3 k R p x ⊗ₜ[k] m) =
      ModuleBar.suffix3 k R M p (rawEval k R M 3 (x ⊗ₜ[k] m)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  | tmul a x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, TensorProduct.add_tmul, hx, hy]
    | tmul b x =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, TensorProduct.add_tmul, hx, hy]
      | tmul c d =>
        change (p a b c * d) • m = p a b c • (d • m)
        exact mul_smul _ _ _

theorem rawEval_suffix (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (x : AbsoluteBar.object k R (n+3)) (m : M) :
    rawEval k R M n (AbsoluteBar.suffixComparison k R p n x ⊗ₜ[k] m) =
      ModuleBar.suffixComparison k R M p n (rawEval k R M (n+3) (x ⊗ₜ[k] m)) := by
  induction n with
  | zero => exact rawEval_suffix_zero k R M p x m
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul a x =>
      rw [AbsoluteBar.suffixComparison_succ_tmul k R p n, rawEval_succ,
        rawEval_succ, ModuleBar.suffixComparison_succ_tmul k R M p n, ih]

end ArExplicit.BarBalanced

end

end OAI
