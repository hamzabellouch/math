import OAI.Geometry.SurfaceImmersion.Primitive.PhaseCurveCrossings

namespace OAI

/-! Both ordered crossings and both pure second forms in either fixed
curve chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

def directionIn (p : M) : SmallModes.Base :=
  fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (d.index : M) d.phase) (c.coordinate p) dy

lemma second_in_chart {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hc : p ∈ c.carrier) (hd : p ∈ d.carrier) :
    c.second F p = realSecondForm (B.phaseRealChartMap d.index d.phase.symm F)
      (c.directionIn d p) (c.directionIn d p) (d.coordinate p) :=
  c.second_transition B d.index d.phase d.smooth d.inverse_smooth hF hc (d.source hd) (d.active p hd)

lemma reverse_crossing_in_chart {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M} (hc : p ∈ c.carrier) (hd : p ∈ d.carrier) :
    let H := B.phaseRealChartMap d.index d.phase.symm F
    c.crossing d F p = orderedCrossing H (c.directionIn d p) dy (d.coordinate p)
      (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy)
        (d.coordinate p)) := by
  have hh := c.crossing_transition d B d.index d.phase d.smooth d.inverse_smooth hF hc hd
    (d.source hd) (d.active p hd)
  have hx : d.coordinate p ∈ (surfacePhaseChart (d.index : M) d.phase).target :=
    (surfacePhaseChart (d.index : M) d.phase).map_source (d.source hd)
  dsimp only at hh ⊢
  change c.crossing d F p = orderedCrossing _ (c.directionIn d p)
    (fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (d.index : M) d.phase) (d.coordinate p) dy)
    (d.coordinate p) _ at hh
  rw [surfacePhaseTransition_self_fderiv _ _ hx,ContinuousLinearMap.id_apply] at hh
  exact hh

omit [CompactSpace M] in
lemma directionIn_continuousOn : ContinuousOn (c.directionIn d) (c.carrier ∩ d.carrier) := by
  let T := surfacePhaseTransition (c.index : M) c.phase (d.index : M) d.phase
  have ht : ContDiffOn ℝ ∞ (fun x => fderiv ℝ T x dy) T.source :=
    ((surfacePhaseTransition_smooth (c.index : M) c.phase c.inverse_smooth
      (d.index : M) d.phase d.smooth).fderiv_of_isOpen T.open_source (by simp)).clm_apply contDiffOn_const
  apply ht.continuousOn.comp (c.coordinate_continuous.mono inter_subset_left)
  intro p hp
  exact surfacePhaseTransition_source _ _ _ _ (c.source hp.1) (d.source hp.2)

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
