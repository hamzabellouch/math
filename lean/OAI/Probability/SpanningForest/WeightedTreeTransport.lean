import OAI.Probability.SpanningForest.WeightedTreeBorel
import OAI.Probability.SpanningForest.USTResponse

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.WeightedTree

theorem partition_eq_sum_trees (K : FiniteSubgraphCode) (h : Field) :
    partition K h = ∑ T : USTResponse.TreeSample K, weight h T.1 := by
  classical
  exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl) (fun T => weight h T)

theorem numerator_eq_sum_trees (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) :
    numerator K e h = ∑ T : USTResponse.TreeSample K,
      if e ∈ T.1 then weight h T.1 else 0 := by
  classical
  unfold numerator
  rw [Finset.sum_filter]
  exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => if e ∈ T then weight h T else 0)

theorem inclusion_eq_of_tree_equiv (K K' : FiniteSubgraphCode)
    (τ : USTResponse.TreeSample K ≃ USTResponse.TreeSample K')
    (a b : Field) (e e' : ℕ × ℕ)
    (hw : ∀ T, weight b (τ T).1 = weight a T.1)
    (he : ∀ T, e' ∈ (τ T).1 ↔ e ∈ T.1) :
    inclusion K' e' b = inclusion K e a := by
  classical
  unfold inclusion
  rw [partition_eq_sum_trees, partition_eq_sum_trees,
    numerator_eq_sum_trees, numerator_eq_sum_trees]
  rw [← τ.sum_comp (fun T => weight b T.1)]
  rw [← τ.sum_comp (fun T => if e' ∈ T.1 then weight b T.1 else 0)]
  simp_rw [hw, he]

end Problem336.WeightedTree

end

end OAI
