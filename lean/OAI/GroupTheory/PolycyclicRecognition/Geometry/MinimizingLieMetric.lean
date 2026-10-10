import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MinimizingMetricChains

namespace OAI

/-! # The published minimizing metric on the connected Lie model

The sole input is the connected Lie-group specialization of J. M. Lee,
*Introduction to Riemannian Manifolds*, second edition, GTM 176 (2018):
Lemma 3.10(b), p. 68 constructs a left-invariant Riemannian metric;
Problem 6-12(c), p. 188 gives completeness of homogeneous metrics;
Corollary 6.21, p. 170 gives minimizing segments; Problem 6-14(a), p. 188
(or the compact exponential-ball argument in Lemma 6.18) gives properness.
Only the resulting metric and normalized minimizing paths are retained.
The large-scale chain property is proved here rather than included in the
published hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- The metric consequences of a complete left-invariant Riemannian metric. -/
structure ProperMinimizingMetric (G : Type*) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace G›
  proper : letI := metric; ProperSpace G
  leftInvariant : letI := metric; IsIsometricSMul G G
  minimizing : letI := metric
    ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|

/-- Precisely the metric specialization of the cited published results;
there is no height, quasi-isometry, or recognition assertion in this input. -/
def LieMinimizingMetricInput : Prop :=
  ∀ S : SimplyConnectedSolvableLieModel, Nonempty (ProperMinimizingMetric S.carrier)

namespace ProperMinimizingMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperMinimizingMetric G)

/-- Sampling minimizing paths provides the chain structure for the existing
proper-homomorphism and canonical-height metric comparisons. -/
def toProperChainMetric : ProperChainMetric G where
  metric := d.metric
  topology_eq := d.topology_eq
  proper := d.proper
  leftInvariant := d.leftInvariant
  chains := by
    let := d.metric
    let := d.leftInvariant
    exact linearMetricChains_of_minimizing_paths d.minimizing

theorem minimizing_compatibleMetric :
    letI := d.toProperChainMetric.compatibleMetric
    ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u| := by
  rw [d.toProperChainMetric.compatibleMetric_eq]
  exact d.minimizing

end ProperMinimizingMetric
end PolycyclicRecognition

end

end OAI
