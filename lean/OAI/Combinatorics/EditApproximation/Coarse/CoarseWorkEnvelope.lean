import OAI.Combinatorics.EditApproximation.Geometry.ChargedQueryAsymptotics
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseWidthCost

namespace OAI

/-! The actual coarse first-request factor times the width budget remains
almost linear. This bound does not assume any seed-correctness event. -/

namespace EditApproximation

open Filter

theorem computed_coarse_widthWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) * computedCoarseWidthOverhead N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computed_weighted_widthWork_near_linear 0 (epsilon / 2) (by linarith),
    subexponential_height_to_input _ (computedCoarseOverheadExponent_tendsto 10)
      (epsilon / 2) (by linarith), eventually_ge_atTop 1] with N hw hc hN
  intro n hn tree hv hd hk
  have hwidth := hw n hn tree hv hd hk
  simp only [pow_zero, mul_one] at hwidth
  have hoverhead := (computedCoarseWidthOverhead_exp_le N (by omega)).trans hc
  calc
    _ ≤ (N + 2 : ℝ) ^ (1 + epsilon / 2) * (N + 2 : ℝ) ^ (epsilon / 2) :=
      mul_le_mul hwidth hoverhead (Nat.cast_nonneg _) (by positivity)
    _ = (N + 2 : ℝ) ^ (1 + epsilon) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N + 2)]
      congr 1
      ring

end EditApproximation

end OAI
