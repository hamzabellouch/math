import OAI.Geometry.SurfaceImmersion.Primitive.CrossingPositivePairing
import OAI.Geometry.SurfaceImmersion.Primitive.LocalIntrinsicCrossing
import OAI.Geometry.Immersion.ClosedSurface.SmoothCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity

namespace OAI

/-! The intrinsic ordered crossing is expressed entirely by the second
fundamental form, and is unchanged under smooth coordinate changes. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open SmallModes RealModes NormalFrame PhaseGeometry

lemma orderedCrossing_intrinsic_eq {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    orderedCrossing F v w p
        (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) =
      (realSecondForm F v w p ⬝ᵥ normalize (realSecondForm F v v p))^2 +
        realSecondForm F v v p ⬝ᵥ realSecondForm F w w p -
          realSecondForm F v w p ⬝ᵥ realSecondForm F v w p := by
  have hgram : gramDet (coordDeriv v F p) (coordDeriv w F p) =
      (v.1*w.2-v.2*w.1)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [coordDeriv_eq_basis F v,coordDeriv_eq_basis F w,gramDet_change_basis]
  have hg := secondForm_gauss_directions hF p v w
  rw [gauss_metric_identity hF p hD,coordinateGauss_eq_curvature_mul F p hD] at hg
  unfold orderedCrossing
  rw [hgram]
  nlinarith only [hg]

lemma orderedCrossing_intrinsic_eq_on {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {p : Base} (hp : p ∈ U) (v w : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    orderedCrossing F v w p
        (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) =
      (realSecondForm F v w p ⬝ᵥ normalize (realSecondForm F v v p))^2 +
        realSecondForm F v v p ⬝ᵥ realSecondForm F w w p -
          realSecondForm F v w p ⬝ᵥ realSecondForm F v w p := by
  obtain ⟨G,hG,_,_,he⟩ := smooth_extension_near hU hF.contMDiffOn hp
  have hd : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0 := by
    simpa only [(coordDeriv_eventuallyEq he dx).eq_of_nhds,
      (coordDeriv_eventuallyEq he dy).eq_of_nhds] using hD
  have hh := orderedCrossing_intrinsic_eq hG.contDiff p v w hd
  unfold orderedCrossing at hh ⊢
  simpa only [(realSecondForm_eventuallyEq he v w).eq_of_nhds,
    (realSecondForm_eventuallyEq he v v).eq_of_nhds,
    (realSecondForm_eventuallyEq he w w).eq_of_nhds,
    (coordDeriv_eventuallyEq he v).eq_of_nhds,(coordDeriv_eventuallyEq he w).eq_of_nhds,
    inducedCurvature_congr_germ he] using hh

lemma orderedCrossing_intrinsic_comp {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p v w : Base)
    (hD : gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    orderedCrossing (F ∘ φ) v w p
      (coordinateGaussianCurvature (realMetric (F ∘ φ) dx dx)
        (realMetric (F ∘ φ) dx dy) (realMetric (F ∘ φ) dy dy) p) =
    orderedCrossing F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p)
      (coordinateGaussianCurvature (realMetric F dx dx)
        (realMetric F dx dy) (realMetric F dy dy) (φ p)) := by
  have hd : gramDet (coordDeriv dx (F ∘ φ) p) (coordDeriv dy (F ∘ φ) p) ≠ 0 := by
    rw [gramDet_comp_smooth hF hφ]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  rw [orderedCrossing_intrinsic_eq (hF.comp hφ) p v w hd,
    orderedCrossing_intrinsic_eq hF (φ p) _ _ hD,
    realSecondForm_comp_smooth hF hφ v w p hD hdet,
    realSecondForm_comp_smooth hF hφ v v p hD hdet,
    realSecondForm_comp_smooth hF hφ w w p hD hdet]

lemma orderedCrossing_intrinsic_germ {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v w : Base) :
    orderedCrossing F v w p
        (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) =
      orderedCrossing G v w p
        (coordinateGaussianCurvature (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p) := by
  unfold orderedCrossing
  simp only [(realSecondForm_eventuallyEq h v w).eq_of_nhds,
    (realSecondForm_eventuallyEq h v v).eq_of_nhds,
    (coordDeriv_eventuallyEq h v).eq_of_nhds,(coordDeriv_eventuallyEq h w).eq_of_nhds,
    inducedCurvature_congr_germ h]

lemma orderedCrossing_intrinsic_comp_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (v w : Base)
    (hD : gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    orderedCrossing (F ∘ φ) v w p
      (coordinateGaussianCurvature (realMetric (F ∘ φ) dx dx)
        (realMetric (F ∘ φ) dx dy) (realMetric (F ∘ φ) dy dy) p) =
    orderedCrossing F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p)
      (coordinateGaussianCurvature (realMetric F dx dx)
        (realMetric F dx dy) (realMetric F dy dy) (φ p)) := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hh := orderedCrossing_intrinsic_comp hG.contDiff hΦ.contDiff p v w hDG
    (by simpa only [eD] using hdet)
  rw [orderedCrossing_intrinsic_germ hecomp v w,eD,ep,
    orderedCrossing_intrinsic_germ heG _ _] at hh
  exact hh

end ClosedSurfaceR4.VelocityFrame

end

end OAI
