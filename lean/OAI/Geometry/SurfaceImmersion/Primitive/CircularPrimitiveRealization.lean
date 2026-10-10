import OAI.Geometry.SurfaceImmersion.Primitive.CircularSupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitivePatchRealization

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

theorem realize_circular_metric
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) {r r₀ R : ℝ} (hr : 0 < r)
    (hrr₀ : r^2 < r₀^2) (hrR : r < R)
    (hpos : ∀ p, 0 < B.weight c.index p ↔ p ∈ circularCoordinateDisk (c.index : M) r₀)
    (hreg : circularCoordinateRegion (c.index : M) r ⊆ (coordinateChart (c.index : M)).target)
    (hfront : c.carrier = circularBoundary (c.index : M) r)
    (hcover : ∀ x ∈ circularCoordinateRegion (c.index : M) r, baseEquiv.symm x ∈ c.phase.source)
    {localPhase : Base → ℝ} (hlocalPhase : ContDiff ℝ ∞ localPhase)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart c.phase x).1 = localPhase x)
    (hconvex : ∀ p ∈ tsupport (B.weight c.index),
      ‖coordinateChart (c.index : M) p-coordinateChart (c.index : M) (c.index : M)‖ ≤ R →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g (c.index : M))
        localPhase (coordinateChart (c.index : M) p) v v)
    (hboundary : ∀ p ∈ c.carrier, c.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c.second F p))
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p)
    (hamppos : ∀ p, 0 < amp p ↔ p ∈ circularCoordinateDisk (c.index : M) r)
    (hphi : ∀ p ∈ circularCoordinateDisk (c.index : M) r,
      phi =ᶠ[𝓝 p] (fun q => (c.phase (chart (c.index : M) q)) 0))
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  obtain ⟨A,i,e,_hindex,_hphase,_hinverse,⟨d⟩⟩ := c.supported_circular_patch hF n hr hrr₀ hrR
    hpos hreg hfront hcover hlocalPhase hphase hconvex hboundary hamp hamp0 hamppos hphi
  exact d.exact_metric data hF h htarget

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
