import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatMean
import OAI.Probability.InvariantIsing.Magnetic.MagneticInverseVariation

namespace OAI

/-! Actual Gaussian continuations in the inverse mean coordinate. The
root equation, rather than a derivative of the inverse, is the premise;
the inverse derivative and drift cancellation are proved here. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticHeatInverse_hasDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v s : ℝ} (hv : 0 < v)
    {b : ℝ → ℝ} (hb : ContinuousAt b v)
    (he : ∀ᶠ t in 𝓝 v, magneticHeatMean P F ζ (t, b t) = s)
    (hq : (P.transition P ζ (Real.toNNReal v) F hF hG dF).first (b v) ≠ 0) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasDerivAt b (-(J.second (b v) / 2 + ζ * J.value (b v) * J.first (b v)) /
      J.first (b v)) v := by
  exact parametric_bias_hasDerivAt hb hq
    (magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv (b v)) he

theorem magneticHeatInverse_curvature_hasDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v s : ℝ} (hv : 0 < v)
    {b : ℝ → ℝ} (hb : ContinuousAt b v)
    (he : ∀ᶠ t in 𝓝 v, magneticHeatMean P F ζ (t, b t) = s)
    (hq : (P.transition P ζ (Real.toNNReal v) F hF hG dF).first (b v) ≠ 0) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasDerivAt (fun t => magneticHeatCurvature P F ζ (t, b t))
      ((J.first (b v)) ^ 2 / 2 *
        (J.third (b v) / (J.first (b v)) ^ 2 -
          (J.second (b v)) ^ 2 / (J.first (b v)) ^ 3) +
        ζ * (J.first (b v)) ^ 2) v := by
  let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
  have hd := inverse_mean_curvature_variation hb hq
    (magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv (b v)) he
    (magneticHeatCurvature_hasFDerivAt P F hF hG dF ζ hv (b v))
  convert hd using 1
  field_simp [hq]
  ring

theorem magneticHeatInverse_continuation_hasDerivAt (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v s : ℝ} (hv : 0 < v)
    {b : ℝ → ℝ} (hb : ContinuousAt b v)
    (he : ∀ᶠ t in 𝓝 v, magneticHeatMean P F ζ (t, b t) = s)
    (hq : (P.transition P ζ (Real.toNNReal v) F hF hG dF).first (b v) ≠ 0) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    let K := A.transition P ζ (Real.toNNReal v) F hF hG dF
    HasDerivAt (fun t => magneticHeatMean A F ζ (t, b t))
      ((J.first (b v)) ^ 2 / 2 *
        (K.second (b v) / (J.first (b v)) ^ 2 -
          K.first (b v) * J.second (b v) / (J.first (b v)) ^ 3)) v := by
  have hd := inverse_mean_curvature_variation hb hq
    (magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv (b v)) he
    (magneticHeatContinuation_hasFDerivAt P A F hF hG dF ζ hv (b v))
  convert hd using 1
  field_simp [hq]
  ring

end InvariantIsing

end

end OAI
