import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetSecondForm
import OAI.Geometry.SurfaceImmersion.Geometry.PureRadialGauss

namespace OAI

/-! The induced Gaussian curvature is a continuous function of the unscaled
second jet on the immersion locus. This controls the new curvature in exterior estimates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame

def boundaryJetCurvature (J : BoundaryProfile) : ℝ :=
  (boundaryJetSecond J dx dx ⬝ᵥ boundaryJetSecond J dy dy -
    boundaryJetSecond J dx dy ⬝ᵥ boundaryJetSecond J dx dy) / gramDet (J 0) (J 1)

lemma boundaryJetCurvature_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    boundaryJetCurvature (realBoundaryProfile F 1 p) =
      coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy)
        (realMetric F dy dy) p := by
  unfold boundaryJetCurvature
  rw [boundaryJetSecond_actual hF,boundaryJetSecond_actual hF,boundaryJetSecond_actual hF,
    gauss_metric_identity hF p hD]
  rfl

lemma continuousAt_boundaryJetCurvature {J : BoundaryProfile}
    (hD : gramDet (J 0) (J 1) ≠ 0) : ContinuousAt boundaryJetCurvature J := by
  have hB (v w : Base) : ContinuousAt (fun H => boundaryJetSecond H v w) J :=
    (continuousAt_boundaryJetSecond v w hD).comp
      (f := fun H => (H,v,w)) (x := J) (by fun_prop)
  have hd : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hg : Continuous (fun H : BoundaryProfile => gramDet (H 0) (H 1)) :=
    contDiff_gram_pair.continuous.comp
      (show Continuous (fun H : BoundaryProfile => (H 0,H 1)) by fun_prop)
  exact ((hd.continuousAt.comp ((hB dx dx).prodMk (hB dy dy))).sub
    (hd.continuousAt.comp ((hB dx dy).prodMk (hB dx dy)))).div hg.continuousAt hD

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
