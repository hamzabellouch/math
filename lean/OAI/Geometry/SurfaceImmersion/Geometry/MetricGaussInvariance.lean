import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateGauss

namespace OAI

/-! The Gauss scalar of an exact realization is fixed by the prescribed metric
in a neighborhood, independent of the choice of immersion. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma coordDeriv_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Base → E} {p : Base} (h : f =ᶠ[𝓝 p] g) (v : Base) :
    coordDeriv v f =ᶠ[𝓝 p] coordDeriv v g :=
  h.fderiv.mono (fun _ he => congrArg (fun L : Base →L[ℝ] E => L v) he)

lemma coordinateGauss_germ {E F G E' F' G' : Base → ℝ} {p : Base}
    (hE : E =ᶠ[𝓝 p] E') (hF : F =ᶠ[𝓝 p] F') (hG : G =ᶠ[𝓝 p] G') :
    coordinateGauss E F G p = coordinateGauss E' F' G' p := by
  simp only [coordinateGauss,hE.eq_of_nhds,hF.eq_of_nhds,hG.eq_of_nhds,
    (coordDeriv_germ hE dx).eq_of_nhds,(coordDeriv_germ hE dy).eq_of_nhds,
    (coordDeriv_germ hF dx).eq_of_nhds,(coordDeriv_germ hF dy).eq_of_nhds,
    (coordDeriv_germ hG dx).eq_of_nhds,(coordDeriv_germ hG dy).eq_of_nhds,
    (coordDeriv_germ (coordDeriv_germ hF dy) dx).eq_of_nhds,
    (coordDeriv_germ (coordDeriv_germ hE dy) dy).eq_of_nhds,
    (coordDeriv_germ (coordDeriv_germ hG dx) dx).eq_of_nhds]

theorem gauss_of_metric_germ {H : RField 4} (hH : ContDiff ℝ ∞ H) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx H p) (coordDeriv dy H p) ≠ 0)
    {E F G : Base → ℝ} (hE : realMetric H dx dx =ᶠ[𝓝 p] E)
    (hF : realMetric H dx dy =ᶠ[𝓝 p] F) (hG : realMetric H dy dy =ᶠ[𝓝 p] G) :
    realSecondForm H dx dx p ⬝ᵥ realSecondForm H dy dy p-
      realSecondForm H dx dy p ⬝ᵥ realSecondForm H dx dy p = coordinateGauss E F G p :=
  (gauss_metric_identity hH p hD).trans (coordinateGauss_germ hE hF hG)

end ClosedSurfaceR4.RealModes

end

end OAI
