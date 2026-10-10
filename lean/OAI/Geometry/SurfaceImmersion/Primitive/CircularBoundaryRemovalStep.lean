import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryMetricStep
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryRemoval
import OAI.Geometry.SurfaceImmersion.Primitive.PreparedCircularDirections

namespace OAI

/-! One actual circular correction removes its own boundary and preserves
all remaining finite geometric conditions. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem circular_boundary_removal_step (curves : ι → PhaseBoundaryCurve B) (a : ι)
    (r r₀ R : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hrr₀ : (r a)^2 < (r₀ a)^2) (hrR : r a < R a)
    (hpos : ∀ p, 0 < B.weight (curves a).index p ↔
      p ∈ circularCoordinateDisk ((curves a).index : M) (r₀ a))
    (hreg : ∀ j, circularCoordinateRegion ((curves j).index : M) (r j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (hcarrier : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j))
    (hcover : ∀ j x, x ∈ circularCoordinateRegion ((curves j).index : M) (r j) →
      baseEquiv.symm x ∈ (curves j).phase.source)
    (ell : ι → Base) (L : ι → ℝ)
    (hphase : ∀ j x, (baseEquiv ((curves j).phase x)).1 =
      centeredConvexPhase (ell j) (L j) (coordinateChart ((curves j).index : M) (curves j).index)
        (baseEquiv x))
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (htan : ∀ j, (circularPhaseTangencies ((curves a).index : M) ((curves j).index : M)
      (ell a) (L a) (r j) (r a)).Finite)
    (hind : ∀ j k, j ≠ k → ∀ p ∈ circularCrossingSet (fun j => ((curves j).index : M)) r,
      p ∈ (coordinateChart ((curves j).index : M)).source →
      p ∈ (coordinateChart ((curves k).index : M)).source →
      covectorDet
        (phaseDerivative (centeredAtlasPhase ((curves j).index : M) (ell j) (L j) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p))
        (phaseDerivative (centeredAtlasPhase ((curves k).index : M) (ell k) (L k) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p)) ≠ 0)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hconvex : ∀ p ∈ tsupport (B.weight (curves a).index),
      ‖coordinateChart ((curves a).index : M) p-coordinateChart ((curves a).index : M) (curves a).index‖ ≤ R a →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((curves a).index : M))
        (centeredConvexPhase (ell a) (L a) (coordinateChart ((curves a).index : M) (curves a).index))
        (coordinateChart ((curves a).index : M) p) v v)
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p)
    (hamppos : ∀ p, 0 < amp p ↔ p ∈ circularCoordinateDisk ((curves a).index : M) (r a))
    (hphi : ∀ p ∈ circularCoordinateDisk ((curves a).index : M) (r a),
      phi =ᶠ[𝓝 p] (fun q => ((curves a).phase (chart ((curves a).index : M) q)) 0))
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => curves j)
          (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ) W N := by
  classical
  apply (curves a).realize_circular_boundary_metric hF n (hr a) hrr₀ hrR hpos (hreg a)
    (hcarrier a) (hcover a) (ell a) (L a)
    (fun x => by exact hphase a (baseEquiv.symm x)) hconvex
    (fun p hp => ⟨hgeom.nonzero a p hp,hgeom.avoids a p hp⟩)
    hamp hamp0 hamppos hphi (fun j : {j : ι // j ≠ a} => curves j)
    (fun j => r j) (fun j => hr j) (fun j => hcarrier j) (fun j => hreg j)
    (fun j k hjk => hpair j k (fun h => hjk (Subtype.ext h)))
    (fun j k l hjk hjl hkl => htriple j k l
      (fun h => hjk (Subtype.ext h)) (fun h => hjl (Subtype.ext h)) (fun h => hkl (Subtype.ext h)))
    (removed_boundary_crossings_disjoint curves a htriple) (hgeom.remove a)
    (hgeom.remove_frontier a) ?_ (fun j => htan j) data h htarget
  intro j p hp hpj
  exact prepared_circular_direction_first curves r hr hcarrier hreg hcover ell L hphase hind a j j.2
    ⟨removed_boundary_crossings_subset curves a hp.1,hp.2⟩ hpj

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
