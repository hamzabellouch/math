import OAI.Combinatorics.EditApproximation.Geometry.LocalArithmeticAsymptotics
import OAI.Combinatorics.EditApproximation.Coarse.CoarseWorkEnvelope

namespace OAI

/-! Multiplying the actual charged dependency-tree work by the concrete
local arithmetic counter preserves the almost-linear exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_widthWork_subexponential (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) * Real.exp (f N) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computed_weighted_widthWork_near_linear 0 (epsilon / 2) (by linarith),
    subexponential_height_to_input f hf (epsilon / 2) (by linarith)] with N hw hfN
  intro n hn tree hv hd hk
  have hwidth := hw n hn tree hv hd hk
  simp only [pow_zero, mul_one] at hwidth
  calc
    _ ≤ (N + 2 : ℝ) ^ (1 + epsilon / 2) * (N + 2 : ℝ) ^ (epsilon / 2) :=
      mul_le_mul hwidth hfN (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N + 2)]
      congr 1
      ring

theorem computed_local_arithmetic_widthWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) *
        localOptimizerArithmeticBudget (integerParameters N).M (integerParameters N).P
          (inputHeight N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computed_widthWork_subexponential computedLocalArithmeticExponent
      computedLocalArithmeticExponent_tendsto epsilon hepsilon,
    eventually_ge_atTop 1, inputHeight_real_tendsto.eventually (eventually_ge_atTop 64)] with N h hN hH
  intro n hn tree hv hd hk
  exact (mul_le_mul_of_nonneg_left
    (computedLocalOptimizer_arithmetic_exp_bound N (by omega) (by exact_mod_cast hH))
    (Nat.cast_nonneg _)).trans (h n hn tree hv hd hk)

end EditApproximation

end OAI
