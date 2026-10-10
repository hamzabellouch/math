import OAI.Geometry.SurfaceImmersion.Primitive.ReferenceCircularMargins
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFrameBounds
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteScalarBounds

namespace OAI

/-! A positive coefficient lower bound fixed on the full reference atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance lowerFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance lowerFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance lowerDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance lowerDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem coefficient_lower : ∃ k : ℝ, 0 < k ∧
    ∀ (a : d.B.centers × Fin 3) p, p ∈ tsupport (d.B.weight a.1) →
      k ≤ d.B.primitiveCoefficientField d.basis a p (gref.inner p) := by
  have hlocal (a : d.B.centers × Fin 3) : ∃ k : ℝ, 0 < k ∧
      ∀ y ∈ (d.B.chartWeightCompact a.1 : Set JetPolynomial.Base),
        k ≤ d.chartCoefficient a.1 a.2 y (d.chartReference a.1 y) := by
    apply (d.B.chartWeightCompact a.1).isCompact.exists_forall_le'
    · exact (d.chartCoefficient_smoothOn a.1 a.2).continuousOn.clm_apply
        (d.chartReference_smooth a.1).continuous.continuousOn
    · exact fun y hy => d.chartCoefficient_positive a.1 a.2 hy
  choose k hk hb using hlocal
  obtain ⟨K,hK,hle⟩ := finite_positive_lower hk
  refine ⟨K,hK,?_⟩
  intro a p hp
  have h := hb a (chart (a.1 : M) p) ⟨p,hp,rfl⟩
  change k a ≤ (d.basis a.1 (chart (a.1 : M) p)).Q a.2
    (fiberToThree (fiberFromThree (d.B.tensorChartRead a.1 gref.inner (chart (a.1 : M) p)))) at h
  rw [fiberToThree_fromThree,d.B.tensorChartRead_on_weight a.1 gref.inner hp] at h
  exact (hle a).trans h

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
