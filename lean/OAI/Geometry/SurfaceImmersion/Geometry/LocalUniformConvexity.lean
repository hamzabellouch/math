import OAI.Geometry.SurfaceImmersion.Atlas.UniformAtlasConvexPhases
import OAI.Geometry.SurfaceImmersion.Atlas.PrescribedAtlasPatch
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasTensorBounds

namespace OAI

/-! Local phase convexity chosen from a fixed background norm, before the
finite circular atlas is selected. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem local_uniform_convexity (g : SmoothMetric M) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K) (p : M) :
    ∃ (L : ℝ) (U : Set M), 0 < L ∧ IsOpen U ∧ p ∈ U ∧
      U ⊆ (coordinateChart p).source ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
        ∀ q ∈ U, ∀ ell : Base, ‖ell‖ ≤ K → ∀ v : Base,
          (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h p)
            (centeredConvexPhase ell L (coordinateChart p p)) (coordinateChart p q) v v := by
  obtain ⟨B,i,hip,hpos,_hsupport,_hnon,houter⟩ :=
    exists_smoothingAtlas_prescribed_patch p (isCompact_singleton : IsCompact ({p} : Set M))
      (mem_singleton p) (chart p).open_source
      (singleton_subset_iff.mpr (by rw [chart_source]; exact mem_chart_source Plane p))
      (Subset.refl _)
  obtain ⟨D,hD,hchange⟩ := A.tensorWeightedBound_change_atlas B 1
  obtain ⟨L,r,hL,hr,hconvex⟩ := B.uniform_atlas_convex_phases g hc
    (mul_nonneg hD hC) hK houter
  let U : Set M := {q | 0 < B.weight i q} ∩
    ((coordinateChart p).source ∩ (coordinateChart p) ⁻¹' Metric.ball (coordinateChart p p) r)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (B.weight_smooth i).continuous).inter
      ((coordinateChart p).isOpen_inter_preimage Metric.isOpen_ball)
  have hp : p ∈ U := by
    refine ⟨hpos p (mem_singleton p),?_,?_⟩
    · rw [coordinateChart_source]; exact mem_chart_source Plane p
    · exact Metric.mem_ball_self hr
  refine ⟨L,U,hL,hU,hp,fun q hq => hq.2.1,?_⟩
  intro h hb hlower q hq ell hell v
  have hb' := hchange h.inner 1 C zero_lt_one le_rfl hC h.contMDiff hb
  have hqi : q ∈ tsupport (B.weight i) := subset_tsupport _ hq.1.ne'
  have hsmall : ‖coordinateChart (i : M) q-coordinateChart (i : M) (i : M)‖ ≤ r := by
    rw [hip]
    have hs : coordinateChart p q ∈ Metric.ball (coordinateChart p p) r := hq.2.2
    exact (by simpa only [Metric.mem_ball,dist_eq_norm] using hs :
      ‖coordinateChart p q-coordinateChart p p‖ < r).le
  have hh := hconvex h hb' hlower i q hqi hsmall ell hell v
  simpa only [hip] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
