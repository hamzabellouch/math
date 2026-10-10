import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability
import OAI.Combinatorics.BalancedRyser.Probability.PatternModelExpansion
import OAI.Combinatorics.BalancedRyser.Probability.PatternOrderingAdapter

namespace OAI

open scoped BigOperators

namespace Balanced.PatternModelMoments
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

theorem centered_moment_bound_of_weight_costs
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    (s : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (W : List P.Label → ℝ)
    (hW : ∀ pre, 0 ≤ W pre) (hnil : W [] = 1)
    (hperm : ∀ pre post, pre.Perm post → W pre = W post)
    (henvelope : ∀ a : Fin (2 * s) → P.Label,
      W (List.ofFn a).reverse =
        P.fixedExpectation K x (fun ω => ∏ j,
          (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j)))))
    (hfree : ∀ pre, pre.length < 2 * s →
      (∑ a, W (a :: pre)) ≤ (C * q) * W pre)
    (htouch : ∀ pre, pre.length < 2 * s →
      (∑ a, if PatternMoments.supportOverlap P.support K pre a then W (a :: pre) else 0) ≤
        C * W pre) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s) * q ^ s := by
  classical
  calc
    P.fixedExpectation K x
        (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
        ∑ a : Fin (2 * s) → P.Label,
          if noIsolated P K a then
            P.fixedExpectation K x (fun ω => ∏ j,
              (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j))))
          else 0 := centered_moment_le_noIsolated P K x s
    _ = ∑ a : Fin (2 * s) → P.Label,
          if noIsolated P K a then W (List.ofFn a).reverse else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> first | exact (henvelope a).symm | rfl
    _ ≤ ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s) * q ^ s := by
      exact PatternMoments.weighted_ordering_bound W
        (PatternMoments.supportOverlap P.support K) (2 * s) s C q hC hq
        (noIsolated P K) hW hnil hperm hfree htouch
        (fun a ha => PatternMoments.exists_support_schedule P.support K a ha)

end Balanced.PatternModelMoments

namespace Balanced.PatternModelMoments
attribute [local instance] Classical.propDecidable

theorem productWeight_ofFn_reverse
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    (n : ℕ) (a : Fin n → P.Label) :
    P.productWeight K x (List.ofFn a).reverse =
      P.fixedExpectation K x (fun ω => ∏ j,
        (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j)))) := by
  unfold PatternModel.productWeight PatternModel.positiveProduct
  congr 1
  funext ω
  simp [List.prod_ofFn]

theorem centered_moment_bound_of_productWeight_costs
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    (s : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hfree : ∀ pre, pre.length < 2 * s →
      (∑ a, P.productWeight K x (a :: pre)) ≤ (C * q) * P.productWeight K x pre)
    (htouch : ∀ pre, pre.length < 2 * s →
      (∑ a, if PatternMoments.supportOverlap P.support K pre a then
        P.productWeight K x (a :: pre) else 0) ≤ C * P.productWeight K x pre) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s) * q ^ s := by
  apply centered_moment_bound_of_weight_costs P K x s q C hq hC
    (P.productWeight K x) (P.productWeight_nonneg K x) (P.productWeight_nil K x)
  · intro pre post h
    exact P.productWeight_perm K x h
  · exact productWeight_ofFn_reverse P K x (2 * s)
  · exact hfree
  · exact htouch

end Balanced.PatternModelMoments

end OAI
