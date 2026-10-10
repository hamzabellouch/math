import OAI.Geometry.SurfaceImmersion.Atlas.PhaseOrdinaryCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionRegularity

namespace OAI

/-! Prepared point inequalities transported into the fixed curve charts. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

lemma crossing_pos_of_coordinate_crossings {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M}
    (hc : p ∈ c.carrier) (hd : p ∈ d.carrier)
    (hpos : ∀ v w : Base, v ≠ 0 → w ≠ 0 →
      0 < orderedCrossing (coordinateMap F (c.index : M)) v w (coordinateChart (c.index : M) p)
        (coordinateGaussianCurvature (realMetric (coordinateMap F (c.index : M)) dx dx)
          (realMetric (coordinateMap F (c.index : M)) dx dy)
          (realMetric (coordinateMap F (c.index : M)) dy dy) (coordinateChart (c.index : M) p))) :
    0 < c.crossing d F p := by
  let e := OpenPartialHomeomorph.refl JetPolynomial.Base
  have he : ContDiff ℝ ∞ e := contDiff_id
  have hi : ContDiff ℝ ∞ e.symm := contDiff_id
  have hpc : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hc
  have hpd : p ∈ (surfacePhaseChart (d.index : M) d.phase).source := d.source hd
  have hpi : p ∈ (surfacePhaseChart (c.index : M) e).source := by
    rw [surfacePhaseChart_refl_source]
    rw [coordinateChart_source,← chart_source]
    exact (c.source hc).1
  have hx := surfacePhaseTransition_source (c.index : M) (c.index : M) c.phase e hpc hpi
  let w := d.directionIn c p
  have hdy : (dy : Base) ≠ 0 := by simp [dy]
  have hw : w ≠ 0 := by
    intro hz
    have hinj := surfacePhaseTransition_fderiv_injective (d.index : M) (c.index : M)
      d.phase c.phase d.smooth d.inverse_smooth c.smooth c.inverse_smooth hpd hpc
    change Function.Injective (fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (c.index : M) c.phase) (d.coordinate p)) at hinj
    exact hdy (hinj (by simpa only [w,directionIn,map_zero] using hz))
  have hI := surfacePhaseTransition_fderiv_injective (c.index : M) (c.index : M)
    c.phase e c.smooth c.inverse_smooth he hi hpc hpi
  change Function.Injective (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (c.index : M) e) (c.coordinate p)) at hI
  have hIv : fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (c.index : M) e)
      (c.coordinate p) dy ≠ 0 := fun hz => hdy (hI (by simpa only [map_zero] using hz))
  have hIw : fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (c.index : M) e)
      (c.coordinate p) w ≠ 0 := fun hz => hw (hI (by simpa only [map_zero] using hz))
  have ht := B.phase_intrinsic_crossing_transition B c.index c.index c.phase e
    c.smooth c.inverse_smooth he hi hF hx
    (by rw [(surfacePhaseChart (c.index : M) c.phase).left_inv hpc]; exact c.active p hc) (by rw [(surfacePhaseChart (c.index : M) c.phase).left_inv hpc]; exact c.active p hc) dy w
  have htp : surfacePhaseTransition (c.index : M) c.phase (c.index : M) e (c.coordinate p) =
      coordinateChart (c.index : M) p :=
    surfacePhaseTransition_apply (c.index : M) (c.index : M) c.phase e hpc
  have hg := B.phaseRealChartMap_surface_germ c.index e F
    ((surfacePhaseChart (c.index : M) e).map_source hpi)
    (by rw [(surfacePhaseChart (c.index : M) e).left_inv hpi]; exact c.active p hc)
  rw [surfacePhaseMap_refl] at hg
  have hh := orderedCrossing_intrinsic_germ hg
    (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (c.index : M) e) (c.coordinate p) dy)
    (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (c.index : M) e) (c.coordinate p) w)
  dsimp only at ht
  change c.crossing d F p = _ at ht
  rw [show surfacePhaseChart (c.index : M) c.phase p = c.coordinate p from rfl] at ht
  rw [surfacePhaseChart_refl_apply] at hh
  rw [ht,htp]
  rw [hh]
  exact hpos _ _ hIv hIw

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
