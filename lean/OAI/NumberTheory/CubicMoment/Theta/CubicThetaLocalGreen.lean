import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGreenAlgebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStarProduct

namespace OAI

/-! The local hyperbolic Green identity for compact C1 tests. Its
only second derivatives are the three pure coordinate derivatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

lemma cubicThetaCoordinateDivergence_integrable (k : CubicThetaAxis) (φ f : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2}) :
    Integrable (cubicThetaCoordinateDivergence k φ f) := by
  have hw := cubicThetaWeightedTest_regular hφ hp
  have hwc := cubicThetaWeightedTest_compact hc
  have hws := (cubicThetaWeightedTest_support φ).trans hp
  have hds := cubicThetaAxisFirst_support k (cubicThetaWeightedTest φ)
  exact (cubicThetaPositiveProduct_integrable hw.continuous hwc hws h₂).add
    (cubicThetaPositiveProduct_integrable (cubicThetaAxisFirst_continuous k hw)
      (hwc.of_isClosed_subset isClosed_closure hds) (hds.trans hws)
      (cubicThetaAxisFirst_continuousOn k hf))

lemma cubicThetaCoordinateDivergence_integral (k : CubicThetaAxis) (φ f : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2})
    (haxis : ∀ p : ℂ × ℝ, 0<p.2 → ContDiffAt ℝ 2
      (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    (∫ p, cubicThetaCoordinateDivergence k φ f p)=0 := by
  have hw := cubicThetaWeightedTest_regular hφ hp
  have hwc := cubicThetaWeightedTest_compact hc
  have hws := (cubicThetaWeightedTest_support φ).trans hp
  have hds := cubicThetaAxisFirst_support k (cubicThetaWeightedTest φ)
  have hA := cubicThetaPositiveProduct_integrable hw.continuous hwc hws h₂
  have hB := cubicThetaPositiveProduct_integrable (cubicThetaAxisFirst_continuous k hw)
    (hwc.of_isClosed_subset isClosed_closure hds) (hds.trans hws)
    (cubicThetaAxisFirst_continuousOn k hf)
  simp only [cubicThetaCoordinateDivergence]
  rw [integral_add (f:=fun p => cubicThetaWeightedTest φ p*cubicThetaAxisSecond k f p)
      (g:=fun p => cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p*cubicThetaAxisFirst k f p) hA hB,
    cubicThetaCoordinate_integrationByParts k f _ hw hwc hws hf h₂ haxis,neg_add_cancel]

lemma cubicThetaCoordinateLaplacian_continuous (f : ℂ × ℝ → ℂ)
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ∀ k, ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2}) :
    ContinuousOn (cubicThetaCoordinateLaplacian f) {p : ℂ × ℝ | 0<p.2} :=
  (((Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 2).mul
    (((h₂ .x).add (h₂ .y)).add (h₂ .height))).sub
      ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
        (cubicThetaAxisFirst_continuousOn .height hf))

lemma cubicThetaLocalGreen_identity (φ f : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ∀ k, ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2})
    (haxis : ∀ k (p : ℂ × ℝ), 0<p.2 → ContDiffAt ℝ 2
      (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p)=
      -(∫ p, star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3) := by
  have hL : Integrable (fun p => star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3) := by
    have hdiv : ContinuousOn (fun p => cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3)
        {p : ℂ × ℝ | 0<p.2} :=
      (cubicThetaCoordinateLaplacian_continuous f hf h₂).div
        ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 3)
        (fun p hp => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne'))
    simpa only [mul_div_assoc] using cubicThetaPositiveStarProduct_integrable hφ.continuous hc hp hdiv
  have hterm (k : CubicThetaAxis) : Integrable (fun p => star (cubicThetaAxisFirst k φ p)*
      (cubicThetaHeightInverse p*cubicThetaAxisFirst k f p)) := by
    have hs := cubicThetaAxisFirst_support k φ
    exact cubicThetaPositiveStarProduct_integrable (cubicThetaAxisFirst_continuous k hφ)
      (hc.of_isClosed_subset isClosed_closure hs) (hs.trans hp)
      (cubicThetaHeightInverse_regular.continuousOn.mul (cubicThetaAxisFirst_continuousOn k hf))
  have hP : Integrable (fun p => cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p) := by
    convert ((hterm .x).add (hterm .y)).add (hterm .height) using 1
    funext p
    unfold cubicThetaCoordinatePairing
    simp only [Pi.add_apply]
    ring
  have hD (k : CubicThetaAxis) := cubicThetaCoordinateDivergence_integrable k φ f hφ hc hp hf (h₂ k)
  have hi : (∫ p, star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3)+
      (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p)=0 := by
    rw [← integral_add hL hP]
    have he : (fun p => star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3+
        cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p)=
      (fun p => cubicThetaCoordinateDivergence .x φ f p+cubicThetaCoordinateDivergence .y φ f p+
        cubicThetaCoordinateDivergence .height φ f p) := funext (cubicThetaGreen_identity φ f hφ hp)
    rw [he,integral_add
      (f:=fun p => cubicThetaCoordinateDivergence .x φ f p+cubicThetaCoordinateDivergence .y φ f p)
      (g:=fun p => cubicThetaCoordinateDivergence .height φ f p)
      ((hD .x).add (hD .y)) (hD .height),
      integral_add (f:=fun p => cubicThetaCoordinateDivergence .x φ f p)
        (g:=fun p => cubicThetaCoordinateDivergence .y φ f p) (hD .x) (hD .y)]
    simp only [cubicThetaCoordinateDivergence_integral _ φ f hφ hc hp hf (h₂ _) (haxis _),add_zero]
  exact eq_neg_of_add_eq_zero_right hi

end CubicFirstMoment

end

end OAI
