import OAI.Combinatorics.EditApproximation.Geometry.DependencyExpansion
import OAI.Combinatorics.EditApproximation.Geometry.DependencyPathEnvelope
import OAI.Combinatorics.EditApproximation.Geometry.WeightedTreeWork

namespace OAI

/-! Width-sensitive work summed over an actual finite dependency expansion.
The bound uses its per-layer counts, including earlier edges that descend. -/

namespace EditApproximation

open Finset Filter

namespace DependencyExpansion

def widthWork (M n : ℕ) (tree : DependencyExpansion) : ℕ :=
  tree.depthWeightedCount (fun d => 1 + n ⌈/⌉ M ^ (tree.depth - d))

theorem widthWork_le (M n a b K : ℕ) (hM : 2 ≤ M)
    (tree : DependencyExpansion) (hvalid : tree.Valid a b)
    (hdepth : tree.depth = intervalTreeDepth M n) (hrank : tree.rank ≤ K)
    (overhead : ℝ) (hoverhead : 0 ≤ overhead)
    (hpath : ∀ j ≤ intervalTreeDepth M n,
      (dependencyPathBudget j K a b : ℝ) ≤ (M : ℝ) ^ j * overhead) :
    (tree.widthWork M n : ℝ) ≤
      (((intervalTreeDepth M n + 1) * n + 4 * M * max 1 n : ℕ) : ℝ) * overhead := by
  have hpartition : tree.widthWork M n =
      ∑ j ∈ range (intervalTreeDepth M n + 1),
        tree.layerNodeCount j * (1 + n ⌈/⌉ M ^ j) := by
    unfold widthWork
    rw [depthWeightedCount_eq_layer_sum a b _ tree hvalid]
    rw [hdepth]
    apply sum_congr rfl
    intro j hj
    have hsub : intervalTreeDepth M n - (intervalTreeDepth M n - j) = j := by
      have := mem_range.mp hj
      omega
    rw [hsub]
  rw [hpartition]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∑ j ∈ range (intervalTreeDepth M n + 1),
        ((M : ℝ) ^ j * overhead) * (1 + (n ⌈/⌉ M ^ j : ℕ)) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (show (tree.layerNodeCount j : ℝ) ≤ dependencyPathBudget j K a b by
        exact_mod_cast layerNodeCount_le_budget a b j K tree hvalid hrank).trans
        (hpath j (Nat.le_of_lt_succ (mem_range.mp hj)))
    _ = (∑ j ∈ range (intervalTreeDepth M n + 1),
        (M : ℝ) ^ j * (1 + (n ⌈/⌉ M ^ j : ℕ))) * overhead := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hoverhead
      exact_mod_cast interval_tree_width_work M n hM

theorem computed_widthWork_subpolynomial (C₁ C₂ : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ C₁)
        (inputHeight N ^ (C₂ * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) ≤
        (((intervalTreeDepth (integerParameters N).M n + 1) * n +
          4 * (integerParameters N).M * max 1 n : ℕ) : ℝ) * (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [computed_dependency_path_subpolynomial C₁ C₂ epsilon hepsilon,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200), eventually_ge_atTop 1] with N hp hell hN
  intro n hn tree hv hd hk
  apply widthWork_le (integerParameters N).M n _ _ _
    (computed_branching_bounds N (by omega) hell).1 tree hv hd hk _ (by positivity)
  intro j hj
  exact hp j (hj.trans (intervalTreeDepth_le_computedMax N n hn))

end DependencyExpansion

end EditApproximation

end OAI
