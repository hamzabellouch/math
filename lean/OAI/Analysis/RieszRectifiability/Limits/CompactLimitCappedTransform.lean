import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitCappedL2
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransformL2

namespace OAI

/-!
# Capped transforms under compact-test limits

Bilinear bounds inherited by a weak limit yield scalar capped-transform L² bounds
on ball restrictions, with constants controlled by upper growth and truncation bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem compact_limit_scalarCappedTransform_L2_bound {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j)) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated m (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated m (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f : Ambient d →ᵇ ℝ) :
    MemLp (scalarCappedTransform m (ν.restrict (ball a R)) e ε f) 2 (ν.restrict (ball a R)) ∧
      eLpNorm (scalarCappedTransform m (ν.restrict (ball a R)) e ε f) 2 (ν.restrict (ball a R)) ≤
        (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m)) : ℝ≥0∞) * eLpNorm f 2 (ν.restrict (ball a R)) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let := relativelyCompact_restrict_finite ν (ball a R) hcompact
  have hnonneg : 0 ≤ ‖e‖ * ((D : ℝ) + C * 2 ^ m) :=
    mul_nonneg (norm_nonneg _) (add_nonneg D.coe_nonneg (mul_nonneg (hgrowth 0).1 (by positivity)))
  apply scalarCappedTransform_memLp_bound_of_bilinear m (ν.restrict (ball a R)) e ε hε f
    (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m)))
  intro g
  rw [Real.coe_toNNReal _ hnonneg]
  exact compact_limit_capped_bilinear_L2_bound m hm C μ ν hgrowth hweak D hB
    a R hboundary hmass e ε hε f g

end

end RieszRectifiability

end OAI
