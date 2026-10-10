import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve

namespace OAI

/-! An open phase region inside the fixed atlas patch and the uniform
coordinate radius used by the metric convexity estimate. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem phase_metric_region (j : B.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set M} (hKs : K ⊆ (surfacePhaseChart (j : M) e).source)
    (hactive : ∀ p ∈ K, B.weight j p ≠ 0) {r : ℝ}
    (hsmall : ∀ p ∈ K, ‖coordinateChart (j : M) p-coordinateChart (j : M) (j : M)‖ < r) :
    ∃ Ω : Set Base, IsOpen Ω ∧ (surfacePhaseChart (j : M) e) '' K ⊆ Ω ∧
      Ω ⊆ (surfacePhaseChart (j : M) e).target ∧
      ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0 ∧
        ‖coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)-
          coordinateChart (j : M) (j : M)‖ < r := by
  let E := surfacePhaseChart (j : M) e
  let P := {p : M | B.weight j p ≠ 0} ∩
    ((coordinateChart (j : M)).source ∩ (coordinateChart (j : M)) ⁻¹'
      Metric.ball (coordinateChart (j : M) (j : M)) r)
  have hP : IsOpen P := (isOpen_ne.preimage (B.weight_smooth j).continuous).inter
    ((coordinateChart (j : M)).isOpen_inter_preimage Metric.isOpen_ball)
  let W := E.source ∩ P
  have hW : IsOpen W := E.open_source.inter hP
  let Ω := E '' W
  refine ⟨Ω,E.isOpen_image_of_subset_source hW inter_subset_left,?_,?_,?_⟩
  · rintro x ⟨p,hp,rfl⟩
    refine ⟨p,⟨hKs hp,hactive p hp,?_,?_⟩,rfl⟩
    · have hs : p ∈ (chart (j : M)).source := (hKs hp).1
      simpa only [coordinateChart_source,chart_source] using hs
    · simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hsmall p hp
  · rintro x ⟨p,hp,rfl⟩
    exact E.map_source hp.1
  · rintro x ⟨p,hp,rfl⟩
    rw [E.left_inv hp.1]
    exact ⟨hp.2.1,by simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hp.2.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
