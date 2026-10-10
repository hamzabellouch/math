import OAI.Geometry.SurfaceImmersion.Primitive.PreparedPhaseCrossingSlopes
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Primitive.TransverseCircularRadii

namespace OAI

/-! The chosen generic phase covectors give nonvertical remaining directions
at every crossing inside the current primitive disk. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompactSpace M] [T2Space M] [Fintype ι] [DecidableEq ι] in
lemma boundaryCrossingSet_eq_circular (curves : ι → PhaseBoundaryCurve B) (r : ι → ℝ)
    (hc : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j)) :
    boundaryCrossingSet curves univ = circularCrossingSet (fun j => ((curves j).index : M)) r := by
  ext p
  constructor
  · rintro ⟨j,_,k,_,hjk,hj,hk⟩
    exact mem_iUnion.mpr ⟨⟨(j,k),hjk⟩,by rw [← hc j,← hc k]; exact ⟨hj,hk⟩⟩
  · intro hp
    obtain ⟨⟨⟨j,k⟩,hjk⟩,hp⟩ := mem_iUnion.mp hp
    exact ⟨j,mem_univ _,k,mem_univ _,hjk,by simpa only [hc] using hp.1,
      by simpa only [hc] using hp.2⟩

omit [CompactSpace M] [Fintype ι] [DecidableEq ι] in
lemma prepared_circular_direction_first (curves : ι → PhaseBoundaryCurve B)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hc : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j))
    (hreg : ∀ j, circularCoordinateRegion ((curves j).index : M) (r j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (hcover : ∀ j x, x ∈ circularCoordinateRegion ((curves j).index : M) (r j) →
      baseEquiv.symm x ∈ (curves j).phase.source)
    (ell : ι → Base) (L : ι → ℝ)
    (hphase : ∀ j x, (baseEquiv ((curves j).phase x)).1 =
      centeredConvexPhase (ell j) (L j) (coordinateChart ((curves j).index : M) (curves j).index)
        (baseEquiv x))
    (hind : ∀ j k, j ≠ k → ∀ p ∈ circularCrossingSet (fun j => ((curves j).index : M)) r,
      p ∈ (coordinateChart ((curves j).index : M)).source →
      p ∈ (coordinateChart ((curves k).index : M)).source →
      covectorDet
        (phaseDerivative (centeredAtlasPhase ((curves j).index : M) (ell j) (L j) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p))
        (phaseDerivative (centeredAtlasPhase ((curves k).index : M) (ell k) (L k) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p)) ≠ 0)
    (a j : ι) (hja : j ≠ a) {p : M}
    (hp : p ∈ boundaryCrossingSet curves univ ∩ circularCoordinateDisk ((curves a).index : M) (r a))
    (hpj : p ∈ (curves j).carrier) : ((curves j).directionIn (curves a) p).1 ≠ 0 := by
  have hps := B.circular_closed_disk_phase_source (curves a).index (hr a) (hreg a)
    (curves a).phase (hcover a) (subset_closure hp.2)
  have hqj : p ∈ (coordinateChart ((curves j).index : M)).source := by
    rw [coordinateChart_source,← chart_source]
    exact ((curves j).source hpj).1
  have hqa : p ∈ (coordinateChart ((curves a).index : M)).source := by
    rw [coordinateChart_source,← chart_source]
    exact hps.1
  apply (curves j).directionIn_first_ne_of_covectors (curves a) ((curves j).index : M)
    (centeredAtlasPhase ((curves j).index : M) (ell j) (L j))
    (centeredAtlasPhase ((curves a).index : M) (ell a) (L a))
    (centeredPhase_first _ _ _ _ (hphase j)) (centeredPhase_first _ _ _ _ (hphase a))
    hqj hpj hps
  apply hind j a hja p _ hqj hqa
  rw [← boundaryCrossingSet_eq_circular curves r hc]
  exact hp.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
