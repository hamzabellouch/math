import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence
import OAI.Analysis.RieszRectifiability.Limits.WeakCappedL2Bounds
import OAI.Analysis.RieszRectifiability.Kernel.RestrictedTruncationBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem compact_limit_capped_bilinear_L2_bound {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j)) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated m (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated m (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f g : Ambient d →ᵇ ℝ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R))| ≤
      (‖e‖ * ((D : ℝ) + C * 2 ^ m)) * Real.sqrt (∫ x in ball a R, g x ^ 2 ∂ν) *
        Real.sqrt (∫ x in ball a R, f x ^ 2 ∂ν) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let μ' := fun j => relativelyCompactFiniteMeasure (μ j) (ball a R) hcompact
  let ν' := relativelyCompactFiniteMeasure ν (ball a R) hcompact
  have hweak' : Tendsto μ' atTop (𝓝 ν') :=
    compactTestConvergence_restrict_tendsto μ ν hweak (ball a R) measurableSet_ball hcompact hboundary
  have hν' : ν' ≠ 0 := by
    intro hz
    have heq := congrArg (fun ρ : FiniteMeasure (Ambient d) => (ρ : Measure (Ambient d)) univ) hz
    apply hmass
    change (ν.restrict (ball a R)) univ = (0 : Measure (Ambient d)) univ at heq
    simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using! heq
  exact weak_capped_bilinear_bound_of_native_L2 m hm C μ' ν' hweak' hν'
    (fun j => globalGrowth_restrict m C (μ j) (hgrowth j) (ball a R)) D
    (fun j => native_truncation_bound_restrict m (μ j) D (hB j) (ball a R) measurableSet_ball)
    e ε hε f g

end

end RieszRectifiability

end OAI
