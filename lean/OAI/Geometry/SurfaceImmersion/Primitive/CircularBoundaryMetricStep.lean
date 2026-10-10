import OAI.Geometry.SurfaceImmersion.Primitive.CircularSupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitivePatchBoundaryStep
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitivePatchDefiners
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTargetCongruence

namespace OAI

/-! Exact realization of an actual circular primitive from the fixed
metric convexity estimate and preserved boundary-normal condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

theorem realize_circular_boundary_metric
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) {r r₀ R : ℝ} (hr : 0 < r)
    (hrr₀ : r^2 < r₀^2) (hrR : r < R)
    (hpos : ∀ p, 0 < B.weight c.index p ↔ p ∈ circularCoordinateDisk (c.index : M) r₀)
    (hreg : circularCoordinateRegion (c.index : M) r ⊆ (coordinateChart (c.index : M)).target)
    (hfront : c.carrier = circularBoundary (c.index : M) r)
    (hcover : ∀ x ∈ circularCoordinateRegion (c.index : M) r, baseEquiv.symm x ∈ c.phase.source)
    (ell : Base) (L : ℝ)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart c.phase x).1 =
      centeredConvexPhase ell L (coordinateChart (c.index : M) c.index) x)
    (hconvex : ∀ p ∈ tsupport (B.weight c.index),
      ‖coordinateChart (c.index : M) p-coordinateChart (c.index : M) (c.index : M)‖ ≤ R →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g (c.index : M))
        (centeredConvexPhase ell L (coordinateChart (c.index : M) c.index))
        (coordinateChart (c.index : M) p) v v)
    (hboundary : ∀ p ∈ c.carrier, c.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c.second F p))
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p)
    (hamppos : ∀ p, 0 < amp p ↔ p ∈ circularCoordinateDisk (c.index : M) r)
    (hphi : ∀ p ∈ circularCoordinateDisk (c.index : M) r,
      phi =ᶠ[𝓝 p] (fun q => (c.phase (chart (c.index : M) q)) 0))
    {ι : Type*} [Fintype ι] (curves : ι → PhaseBoundaryCurve B) (radii : ι → ℝ)
    (hradii : ∀ j, 0 < radii j)
    (hcarriers : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (radii j))
    (hregions : ∀ j, circularCoordinateRegion ((curves j).index : M) (radii j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (hEf : Disjoint (boundaryCrossingSet curves univ) c.carrier)
    (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hfrontGeom : ∀ j p, p ∈ (curves j).carrier ∩ c.carrier →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < c.crossing (curves j) F p)
    (hfirst : ∀ j p, p ∈ boundaryCrossingSet curves univ ∩ circularCoordinateDisk (c.index : M) r →
      p ∈ (curves j).carrier → ((curves j).directionIn c p).1 ≠ 0)
    (htan : ∀ j, (circularPhaseTangencies (c.index : M) ((curves j).index : M)
      ell L (radii j) r).Finite)
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W, FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) W N := by
  obtain ⟨A,i,e,hi,he,_hinverse,⟨d⟩⟩ := c.supported_circular_patch hF n hr hrr₀ hrR
    hpos hreg hfront hcover (centeredConvexPhase_smooth ell L _) hphase hconvex
    hboundary hamp hamp0 hamppos hphi
  have hdisk : circularCoordinateDisk (c.index : M) r = circularCoordinateDisk (i : M) r := by rw [hi]
  have hphase' : ∀ x, (JetPolynomial.realPhaseChart e x).1 =
      centeredConvexPhase ell L (coordinateChart (i : M) i) x := by
    intro x
    rw [hi]
    change (baseEquiv (e (baseEquiv.symm x))).1 = _
    rw [he]
    exact hphase x
  obtain ⟨P,hP,hlocal⟩ := d.circular_definers ell L r hr hdisk hphase'
    (by simpa only [hi] using hreg) curves radii hradii hcarriers hregions
    (boundaryCrossingSet curves univ) (boundaryCrossingSet_finite curves univ hpair)
    (fun j k hjk p hp => boundaryCrossingSet_pair curves (mem_univ _) (mem_univ _) hjk hp.1 hp.2)
    (by simpa only [hi] using htan)
  have hcf : c.carrier = frontier (circularCoordinateDisk (c.index : M) r) :=
    hfront.trans (circularCoordinateDisk_frontier (c.index : M) hr hreg).symm
  apply d.boundary_step c hi he curves hpair htriple
    (circularCoordinateDisk_open _ _) (circularCoordinateDisk_regular _ hr hreg) hcf
    (by rwa [← hcf]) data hF n hgeom hboundary
    (by simpa only [← hcf] using hfrontGeom) ?_ hP hlocal h htarget
  intro j p hp hpj
  rw [surfacePhaseTransition_target_congr ((curves j).index : M) (i : M) (c.index : M)
    hi (curves j).phase e c.phase he]
  exact hfirst j p hp hpj

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
