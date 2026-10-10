import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientBoundedLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

abbrev QuotientNormBall (C : ℝ≥0) := {x : T.CauchyQuotient hadd // ‖x‖ ≤ C}

@[instance_reducible]
def quotientNormBallMetricSpace (C : ℝ≥0) : MetricSpace (T.QuotientNormBall hadd C) := by
  exact MetricSpace.induced Subtype.val Subtype.val_injective (T.quotientMetricSpace hadd hsqrt)

theorem quotientNormBallCompleteSpace (C : ℝ≥0) :
    @CompleteSpace (T.QuotientNormBall hadd C) (T.quotientNormBallMetricSpace hadd hsqrt C).toUniformSpace := by
  let := T.quotientNormBallMetricSpace hadd hsqrt C
  let : PseudoMetricSpace (T.QuotientNormBall hadd C) :=
    (T.quotientNormBallMetricSpace hadd hsqrt C).toPseudoMetricSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc : T.QuotientIsMetricCauchy hadd hsqrt (fun n => (u n).1) := by
    exact (cauchySeq_iff_tendsto_dist_atTop_0).mp hu
  obtain ⟨x,hx,ht⟩ := T.quotient_bounded_metric_limit hadd hsqrt (fun n => (u n).1) hc C C.2 (fun n => (u n).2)
  refine ⟨⟨x,hx⟩,?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he := (Metric.tendsto_nhds.mp ht) ε hε
  filter_upwards [he] with n hn
  change T.quotientDistance hadd hsqrt (u n).1 x < ε
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)] using hn
end CuntzPureness.PositiveQuasitrace

end

end OAI
