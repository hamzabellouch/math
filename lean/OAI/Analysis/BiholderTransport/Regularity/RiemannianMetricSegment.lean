import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.JensenHessian
import OAI.Analysis.BiholderTransport.Geodesics.MetricSegments

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

namespace WeakMTWTransport
open Set Manifold Bundle
open scoped ContDiff

lemma riemannian_exists_metric_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (x y : M) :
    ∃ γ : Icc (0:ℝ) (dist x y) → M, Isometry γ ∧
      γ ⟨0,⟨le_rfl,dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ = y :=
  exists_metric_segment x y (riemannian_exists_midpoint (I := I))
end WeakMTWTransport

end

end OAI
