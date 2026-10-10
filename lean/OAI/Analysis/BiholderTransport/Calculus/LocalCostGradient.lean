import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayScaling
import OAI.Analysis.BiholderTransport.Calculus.LocalMetricGradient
import OAI.Analysis.BiholderTransport.Coordinates.IntrinsicGradient

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_cost_gradient (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
      ∃ q : TangentBundle 𝓘(ℝ,E) M,
        q.1 = y ∧ ‖q.2‖ = dist b y ∧ (sprayFlow (-1) q).1 = b ∧
        HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun x => dist b x ^ 2 / 2) q.1 (innerSL ℝ q.2) := by
  obtain ⟨δ,τ,hδ,hτ,hsrc,H⟩ := exists_local_metric_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro b hb y hy
  obtain ⟨z,hzb,hzy,hn,hD⟩ := H b hb y hy
  have hzs : (sprayFlow τ z).1 ∈ (extChartAt 𝓘(ℝ,E) a).source := hzy ▸ hsrc hy
  have hDc : HasFDerivAt (fun w : E => dist b ((extChartAt 𝓘(ℝ,E) a).symm w)^2 / 2)
      (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a (sprayFlow τ z).1)
        ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E))
          (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) (sprayFlow τ z)).2))
      (extChartAt 𝓘(ℝ,E) a (sprayFlow τ z).1) := by rwa [hzy]
  have hD' := hasMFDerivAt_of_coordinate_gradient (sprayFlow τ z) hzs
    (fun x => dist b x^2/2) τ hDc
  refine ⟨tangentScale τ (sprayFlow τ z),hzy,?_,?_,?_⟩
  · change ‖τ • (sprayFlow τ z).2‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hτ,sprayFlow_speed]
    exact hn.symm
  · rw [sprayFlow_scale,show τ * (-1) = -τ by ring,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]
    exact hzb
  · exact hD'.congr_mfderiv (map_smul (innerSL ℝ) τ (sprayFlow τ z).2).symm

end WeakMTWTransport

end

end OAI
