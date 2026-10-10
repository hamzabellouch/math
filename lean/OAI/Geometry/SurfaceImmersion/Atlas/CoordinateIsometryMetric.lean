import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricConvexity

namespace OAI

/-! The ordinary coordinate metric of an isometric immersion is the
prescribed metric, independently of atlas partition weights. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateMap_metric_evaluate {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) (q : M) {x : Base}
    (hx : x ∈ coordinateDomain q) (v w : Base) :
    realMetric (coordinateMap F q) v w x = PhaseMean.evaluate (coordinateMetric g q x) v w := by
  have hi := ((coordinateInverse_smoothOn q) x hx).contMDiffAt
    ((coordinateDomain_open q).mem_nhds hx)
  have hm := (hF.1 (coordinateInverse q x)).mdifferentiableAt (by simp)
  have hic := hi.mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hm hic
  rw [mfderiv_eq_fderiv] at hd
  have hs : DifferentiableAt ℝ (F ∘ coordinateInverse q) x := (hm.comp x hic).differentiableAt
  have he : fderiv ℝ (coordinateMap F q) x = spaceCoordinates.toContinuousLinearMap.comp
      ((mfderiv planeModel spaceModel F (coordinateInverse q x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (coordinateInverse q) x)) := by
    change fderiv ℝ (spaceCoordinates ∘ (F ∘ coordinateInverse q)) x = _
    rw [fderiv_comp x spaceCoordinates.differentiableAt hs,spaceCoordinates.fderiv,hd]
    rfl
  rw [coordinateMetric_evaluate]
  change fderiv ℝ (coordinateMap F q) x v ⬝ᵥ fderiv ℝ (coordinateMap F q) x w = _
  rw [he]
  let vv : TangentSpace 𝓘(ℝ,Base) x := v
  let ww : TangentSpace 𝓘(ℝ,Base) x := w
  let dv : TangentSpace planeModel (coordinateInverse q x) :=
    mfderiv 𝓘(ℝ,Base) planeModel (coordinateInverse q) x vv
  let dw : TangentSpace planeModel (coordinateInverse q x) :=
    mfderiv 𝓘(ℝ,Base) planeModel (coordinateInverse q) x ww
  change spaceCoordinates (mfderiv planeModel spaceModel F (coordinateInverse q x) dv) ⬝ᵥ
    spaceCoordinates (mfderiv planeModel spaceModel F (coordinateInverse q x) dw) = g.inner _ dv dw
  exact (spaceCoordinates_dot _ _).trans (hF.2 _ dv dw)

lemma coordinateMap_metric {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) (q : M) {x : Base}
    (hx : x ∈ coordinateDomain q) :
    inducedCoordinateMetric (coordinateMap F q) x = coordinateMetric g q x := by
  ext k
  fin_cases k
  · change realMetric (coordinateMap F q) dx dx x = coordinateMetric g q x 0
    simpa [PhaseMean.evaluate,dx,dy] using coordinateMap_metric_evaluate hF q hx dx dx
  · change realMetric (coordinateMap F q) dx dy x = coordinateMetric g q x 1
    simpa [PhaseMean.evaluate,dx,dy] using coordinateMap_metric_evaluate hF q hx dx dy
  · change realMetric (coordinateMap F q) dy dy x = coordinateMetric g q x 2
    simpa [PhaseMean.evaluate,dx,dy] using coordinateMap_metric_evaluate hF q hx dy dy

end ClosedSurfaceR4

end

end OAI
