import OAI.Geometry.SurfaceImmersion.Geometry.LocalSecondFormNaturality

namespace OAI

/-! Intrinsic curvature and ordered crossings depend only on the local
smooth germ. This applies the radial calculation in an actual chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame PhaseGeometry

lemma realMetric_eventuallyEq {F G : RField 4} {p : Base} (h : F =ᶠ[𝓝 p] G)
    (v w : Base) : realMetric F v w =ᶠ[𝓝 p] realMetric G v w := by
  filter_upwards [coordDeriv_eventuallyEq h v,coordDeriv_eventuallyEq h w] with x hv hw
  simp only [realMetric,hv,hw]

private lemma scalarDeriv_eventuallyEq {f g : Base → ℝ} {p : Base}
    (h : f =ᶠ[𝓝 p] g) (v : Base) : coordDeriv v f =ᶠ[𝓝 p] coordDeriv v g :=
  h.fderiv.mono fun _ hx => congrArg (fun D : Base →L[ℝ] ℝ => D v) hx

lemma coordinateGauss_congr_germ {E F G E' F' G' : Base → ℝ} {p : Base}
    (hE : E =ᶠ[𝓝 p] E') (hF : F =ᶠ[𝓝 p] F') (hG : G =ᶠ[𝓝 p] G') :
    coordinateGauss E F G p = coordinateGauss E' F' G' p := by
  simp only [coordinateGauss,hE.eq_of_nhds,hF.eq_of_nhds,hG.eq_of_nhds,
    (scalarDeriv_eventuallyEq hE dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq hE dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq hF dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq hF dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq hG dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq hG dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq (scalarDeriv_eventuallyEq hF dy) dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq (scalarDeriv_eventuallyEq hE dy) dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq (scalarDeriv_eventuallyEq hG dx) dx).eq_of_nhds]

lemma inducedCurvature_congr_germ {F G : RField 4} {p : Base} (h : F =ᶠ[𝓝 p] G) :
    coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
    coordinateGaussianCurvature (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p := by
  have hE := realMetric_eventuallyEq h dx dx
  have hF := realMetric_eventuallyEq h dx dy
  have hG := realMetric_eventuallyEq h dy dy
  simp only [coordinateGaussianCurvature,coordinateGauss_congr_germ hE hF hG,
    hE.eq_of_nhds,hF.eq_of_nhds,hG.eq_of_nhds]

lemma coordinateGaussianCurvature_pure_radial_on {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {p : Base} (hp : p ∈ U)
    (n : RVec 4) {r : ℝ} (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ v w, realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      (r⁻¹)^2 := by
  obtain ⟨G,hG,_,_,he⟩ := smooth_extension_near hU hF.contMDiffOn hp
  have hd : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0 := by
    simpa only [(coordDeriv_eventuallyEq he dx).eq_of_nhds,
      (coordDeriv_eventuallyEq he dy).eq_of_nhds] using hD
  have hb : ∀ v w, realSecondForm G v w p =
      (r⁻¹*(coordDeriv v G p ⬝ᵥ coordDeriv w G p)) • n := by
    intro v w
    simpa only [(realSecondForm_eventuallyEq he v w).eq_of_nhds,
      (coordDeriv_eventuallyEq he v).eq_of_nhds,
      (coordDeriv_eventuallyEq he w).eq_of_nhds] using hB v w
  rw [← inducedCurvature_congr_germ he]
  exact coordinateGaussianCurvature_pure_radial hG.contDiff p n hn hd hb

lemma orderedCrossing_intrinsic_pure_radial_on {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {p : Base} (hp : p ∈ U)
    (v w : Base) (n : RVec 4) {r : ℝ} (hr : 0 < r) (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ a b, realSecondForm F a b p =
      (r⁻¹*(coordDeriv a F p ⬝ᵥ coordDeriv b F p)) • n)
    (hv : coordDeriv v F p ≠ 0) (hw : coordDeriv w F p ≠ 0) :
    0 < orderedCrossing F v w p
      (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) := by
  rw [coordinateGaussianCurvature_pure_radial_on hU hF hp n hn hD hB]
  exact (orderedCrossing_pure_radial p v w n hr hn hv hw (hB v v) (hB v w)).2

end ClosedSurfaceR4.RealModes

end

end OAI
