import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationTwoJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationPDE

namespace OAI

/-! Spatial derivatives for the minimal bounded test data used by the
variance generator, including the ordinary scalar curvature test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticTwoJet_average_hasDerivAt (P : MagneticContinuationJet)
    (A : MagneticContinuationTwoJet) (F : ℝ → ℝ)
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    HasDerivAt (fieldSpinTransition ζ v F A.value)
      (fieldTiltSpatial ζ v F P.value A.value A.first z) z := by
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨C, hC, bC⟩ := A.bValue
  obtain ⟨D, _, bD⟩ := A.bFirst
  exact hasDerivAt_fieldSpinTransition ζ v hF hG P.mValue A.mValue A.mFirst
    hK hC bK bC bD dF A.dValue z

lemma magneticTwoJet_spatial_hasDerivAt (P : MagneticContinuationJet)
    (A : MagneticContinuationTwoJet) (F : ℝ → ℝ)
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    HasDerivAt (fieldTiltSpatial ζ v F P.value A.value A.first)
      (magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second z) z := by
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨L, hL, bL⟩ := P.bFirst
  obtain ⟨a, ha, ba⟩ := A.bValue
  obtain ⟨b, hb, bb⟩ := A.bFirst
  obtain ⟨c, _, bc⟩ := A.bSecond
  exact hasDerivAt_magneticContinuationSecond ζ v hF hG P.mValue P.mFirst
    A.mValue A.mFirst A.mSecond hK hL ha hb bK bL ba bb bc dF P.dValue
    A.dValue A.dFirst z

end InvariantIsing

end

end OAI
