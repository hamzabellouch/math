import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionCocycle

namespace OAI

/-! Intrinsic ordered crossing invariants for the fixed later curves.
Their values can be computed in whichever phase chart is being corrected. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

def crossing (F : M → Space) (p : M) : ℝ :=
  let H := B.phaseRealChartMap c.index c.phase.symm F
  let T := surfacePhaseTransition (d.index : M) d.phase (c.index : M) c.phase
  let v := fderiv ℝ T (d.coordinate p) dy
  orderedCrossing H dy v (c.coordinate p)
    (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy)
      (c.coordinate p))

lemma crossing_transition (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hc : p ∈ c.carrier) (hd : p ∈ d.carrier)
    (hp : p ∈ (surfacePhaseChart (i : M) e).source) (hw : A.weight i p ≠ 0) :
    let H := A.phaseRealChartMap i e.symm F
    let vc := fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy
    let vd := fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (i : M) e) (d.coordinate p) dy
    let q := baseEquiv (e (chart (i : M) p))
    c.crossing d F p = orderedCrossing H vc vd q
      (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q) := by
  have hpc : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hc
  have hpd : p ∈ (surfacePhaseChart (d.index : M) d.phase).source := d.source hd
  have hback : (surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p) = p :=
    (surfacePhaseChart (c.index : M) c.phase).left_inv hpc
  have hx : c.coordinate p ∈ (surfacePhaseTransition (c.index : M) c.phase (i : M) e).source :=
    surfacePhaseTransition_source _ _ _ _ hpc hp
  let u := fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (c.index : M) c.phase)
    (d.coordinate p) dy
  have ht := B.phase_intrinsic_crossing_transition A c.index i c.phase e c.smooth c.inverse_smooth
    he hi hF hx (by rw [hback]; exact c.active p hc) (by rwa [hback]) dy u
  have hq : surfacePhaseTransition (c.index : M) c.phase (i : M) e (c.coordinate p) =
      baseEquiv (e (chart (i : M) p)) := surfacePhaseTransition_apply _ _ _ _ hpc
  have hcoc := surfacePhaseTransition_fderiv_cocycle (d.index : M) (c.index : M) (i : M)
    d.phase c.phase e d.inverse_smooth c.smooth c.inverse_smooth he hpd hpc hp
  have hvec : fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) u =
      fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (i : M) e) (d.coordinate p) dy := by
    exact (congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L dy) hcoc).symm
  dsimp only at ht ⊢
  change c.crossing d F p = _ at ht
  rw [hq,hvec] at ht
  exact ht

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
