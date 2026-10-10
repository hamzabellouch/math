import OAI.Geometry.SurfaceImmersion.Primitive.ConstructSupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegion
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseFrontierAvoidance
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseBoundaryCurve

namespace OAI

/-! The analytic support and all local geometric data for an actual circular
primitive are constructed from the preserved boundary normal and metric bound. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

theorem supported_circular_patch
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
      phi =ᶠ[𝓝 p] (fun q => (c.phase (chart (c.index : M) q)) 0)) :
    ∃ (A : SmoothingAtlas M) (i : A.centers)
      (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base),
      (i : M) = (c.index : M) ∧ (∀ x, e x = c.phase x) ∧ (∀ x, e.symm x = c.phase.symm x) ∧
      Nonempty (SupportedPrimitivePatch A i e F amp phi (circularCoordinateDisk (c.index : M) r)) := by
  let D := circularCoordinateDisk (c.index : M) r
  have hD : IsOpen D := circularCoordinateDisk_open (c.index : M) r
  have hDs : closure D ⊆ (surfacePhaseChart (c.index : M) c.phase).source :=
    B.circular_closed_disk_phase_source c.index hr hreg c.phase hcover
  have hDj : (c.index : M) ∈ D := by
    refine ⟨?_,?_⟩
    · rw [coordinateChart_source]
      exact mem_chart_source Plane (c.index : M)
    · change circularRadiusSquared (coordinateChart (c.index : M) (c.index : M))
        (coordinateChart (c.index : M) (c.index : M)) < r^2
      simp only [circularRadiusSquared,sub_self,zero_pow (by decide : 2 ≠ 0),add_zero]
      exact sq_pos_of_pos hr
  have hclosed (p : M) (hp : p ∈ closure D) :
      p ∈ (coordinateChart (c.index : M)).source ∧
        circularRadiusSquared (coordinateChart (c.index : M) (c.index : M))
          (coordinateChart (c.index : M) p) ≤ r^2 := by
    have hc : closure D = circularDiskClosure (c.index : M) r :=
      circularCoordinateDisk_closure (c.index : M) hr hreg
    exact (circularDiskClosure_iff (c.index : M) hreg p).mp (hc ▸ hp)
  have hw (p : M) (hp : p ∈ closure D) : B.weight c.index p ≠ 0 := by
    apply ne_of_gt ((hpos p).mpr ?_)
    exact ⟨(hclosed p hp).1,((hclosed p hp).2).trans_lt hrr₀⟩
  have hsmall (p : M) (hp : p ∈ closure D) :
      ‖coordinateChart (c.index : M) p-coordinateChart (c.index : M) (c.index : M)‖ < R := by
    have hh := circularRadiusSquared_le_norm (hclosed p hp).2
    rw [abs_of_pos hr] at hh
    exact hh.trans_lt hrR
  obtain ⟨Ω,hΩ,hDΩ,hΩe,hΩprop⟩ := B.phase_metric_region c.index c.phase hDs hw hsmall
  have hcv : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (c.index : M)) localPhase
        (coordinateChart (c.index : M) ((surfacePhaseChart (c.index : M) c.phase).symm x)) v v := by
    intro x hx v hv
    exact hconvex _ (subset_tsupport _ (hΩprop x hx).1) (hΩprop x hx).2.le v hv
  have hb := c.frontier_avoidance hD hDs
    (hfront.trans (circularCoordinateDisk_frontier (c.index : M) hr hreg).symm) n hboundary
  exact B.construct_supported_primitive_patch c.index hF n c.phase c.smooth c.inverse_smooth
    hD hDj hDs hΩ hDΩ hΩe (fun x hx => (hΩprop x hx).1)
    hlocalPhase hphase hcv hb hamp hamp0 hamppos hphi

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
