import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveLocalization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAxisLineDerivative
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace OAI

/-! Integration by parts for the pure coordinate derivatives, with
compact positive-height tests and no assumption on mixed derivatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

lemma cubicThetaAxisFirst_continuousOn (k : CubicThetaAxis) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2}) :
    ContinuousOn (cubicThetaAxisFirst k f) {p : ℂ × ℝ | 0<p.2} := by
  have hc := (hf.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_snd)
    (by norm_num)).clm_apply (continuousOn_const (c:=cubicThetaAxisVector k))
  apply hc.congr
  intro p hp
  exact cubicThetaAxisFirst_eq_fderiv k f
    ((hf.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num))

lemma cubicThetaCoordinate_integrationByParts (k : CubicThetaAxis) (f φ : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (hf₂ : ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2})
    (haxis : ∀ p : ℂ × ℝ, 0<p.2 → ContDiffAt ℝ 2
      (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    (∫ p, φ p*cubicThetaAxisSecond k f p)=
      -(∫ p, cubicThetaAxisFirst k φ p*cubicThetaAxisFirst k f p) := by
  have hdf := cubicThetaAxisFirst_continuousOn k hf
  have hdφ := cubicThetaAxisFirst_continuous k hφ
  have hdφs := cubicThetaAxisFirst_support k φ
  have hdφc : HasCompactSupport (cubicThetaAxisFirst k φ) := hc.of_isClosed_subset isClosed_closure hdφs
  have hi₁ := cubicThetaPositiveProduct_integrable hdφ hdφc (hdφs.trans hp) hdf
  have hi₂ := cubicThetaPositiveProduct_integrable hφ.continuous hc hp hf₂
  have hi₀ := cubicThetaPositiveProduct_integrable hφ.continuous hc hp hdf
  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B:=ContinuousLinearMap.mul ℝ ℂ) hi₁ hi₂ hi₀
    (fun p _ => by
      rw [cubicThetaAxisFirst_eq_fderiv k φ (hφ.differentiable one_ne_zero p)]
      exact (hφ.differentiable one_ne_zero p).hasFDerivAt.hasLineDerivAt (cubicThetaAxisVector k))
    (fun p h => cubicThetaAxisFirst_hasLineDerivAt k f p (haxis p (hp h)))

end CubicFirstMoment

end

end OAI
