import OAI.Geometry.SurfaceImmersion.Atlas.JetMetricCoordinatePullback

namespace OAI

/-! The actual phase chart in the real pair coordinates used by curvature. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial

def realPhaseChart (e : OpenPartialHomeomorph Base Base) :
    OpenPartialHomeomorph SmallModes.Base SmallModes.Base :=
  (planeCoordinateIsometry.symm.toHomeomorph.transOpenPartialHomeomorph e).transHomeomorph
    planeCoordinateIsometry.toHomeomorph

lemma realPhaseChart_apply (e : OpenPartialHomeomorph Base Base) (x : SmallModes.Base) :
    realPhaseChart e x = planeCoordinateIsometry (e (planeCoordinateIsometry.symm x)) := rfl

lemma realPhaseChart_symm_apply (e : OpenPartialHomeomorph Base Base) (x : SmallModes.Base) :
    (realPhaseChart e).symm x = planeCoordinateIsometry (e.symm (planeCoordinateIsometry.symm x)) := rfl

lemma realPhaseChart_source (e : OpenPartialHomeomorph Base Base) :
    (realPhaseChart e).source = planeCoordinateIsometry.symm ⁻¹' e.source := rfl

lemma realPhaseChart_target (e : OpenPartialHomeomorph Base Base) :
    (realPhaseChart e).target = planeCoordinateIsometry.symm ⁻¹' e.target := rfl

lemma realPhaseChart_smooth (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (realPhaseChart e) :=
  planeCoordinateIsometry.contDiff.comp (he.comp planeCoordinateIsometry.symm.contDiff)

lemma realPhaseChart_symm_smooth (e : OpenPartialHomeomorph Base Base) (hi : ContDiff ℝ ∞ e.symm) :
    ContDiff ℝ ∞ (realPhaseChart e).symm :=
  planeCoordinateIsometry.contDiff.comp (hi.comp planeCoordinateIsometry.symm.contDiff)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
