import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatCurvature

namespace OAI

/-! Joint heat derivatives of the mean spin and of a bounded continuation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatMean (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage q.1 ζ F P.value q.2

lemma magneticHeatMean_eq (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatMean P F ζ q =
      fieldSpinTransition ζ (Real.toNNReal q.1) F P.value q.2 := by
  exact congrFun (field_gaussianTiltAverage_eq_transition q.1 ζ hF P.mValue) q.2

theorem magneticHeatMean_hasFDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatMean P F ζ)
      (pairLinear (J.second z / 2 + ζ * J.value z * J.first z)
        (J.first z)) (v, z) := by
  exact magneticGaussianAverageTwo_hasFDerivAt_generator P P.toTwoJet F hF hG dF ζ hv z

theorem magneticHeatContinuation_hasFDerivAt (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    let K := A.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatMean A F ζ)
      (pairLinear (K.second z / 2 + ζ * J.value z * K.first z)
        (K.first z)) (v, z) := by
  exact magneticGaussianAverageTwo_hasFDerivAt_generator P A.toTwoJet F hF hG dF ζ hv z

end InvariantIsing

end

end OAI
