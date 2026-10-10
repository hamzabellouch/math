import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationGenerator
import OAI.Probability.InvariantIsing.Fields.FieldRealVariance

namespace OAI

/-! The actual bounded continuation solves the scalar heat equation with
the nonlinear backward-field drift. The first coordinate is the amount
of Gaussian variance already applied; reversing it gives the backward
time convention in the manuscript. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticGaussianSpaceTwo_eq (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (ζ v z : ℝ) :
    magneticGaussianSpace ζ v F P.value A.value A.first z =
      fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z := by
  unfold magneticGaussianSpace fieldTiltSpatial
  rw [field_gaussianTiltAverage_eq_transition v ζ hF A.mFirst,
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.value y * P.value y)
      hF (A.mValue.mul P.mValue),
    field_gaussianTiltAverage_eq_transition v ζ hF A.mValue,
    field_gaussianTiltAverage_eq_transition v ζ hF P.mValue]

lemma magneticGaussianGeneratorTwo_eq (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (ζ v z : ℝ) :
    magneticGaussianGenerator ζ v F P.value P.first A.value A.first A.second z =
      magneticContinuationSecond ζ (Real.toNNReal v) F P.value P.first
          A.value A.first A.second z / 2 +
        ζ * fieldSpinTransition ζ (Real.toNNReal v) F P.value z *
          fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z := by
  rw [magneticContinuation_secondTwo_generator P A F hF hG]
  dsimp only [magneticGaussianGenerator]
  rw [field_gaussianTiltAverage_eq_transition v ζ hF A.mSecond,
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.first y * P.value y)
      hF (A.mFirst.mul P.mValue),
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.value y * P.first y)
      hF (A.mValue.mul P.mFirst),
    field_gaussianTiltAverage_eq_transition v ζ hF A.mValue,
    field_gaussianTiltAverage_eq_transition v ζ hF P.mFirst,
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.value y * (P.value y) ^ 2)
      hF (A.mValue.mul (P.mValue.pow_const 2)),
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => (P.value y) ^ 2)
      hF (P.mValue.pow_const 2)]

theorem magneticGaussianAverageTwo_hasFDerivAt_generator (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.value q.2)
      (pairLinear
        (magneticContinuationSecond ζ (Real.toNNReal v) F P.value P.first
            A.value A.first A.second z / 2 +
          ζ * fieldSpinTransition ζ (Real.toNNReal v) F P.value z *
            fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z)
        (fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z)) (v, z) := by
  have hd := magneticGaussianAverageTwo_hasFDerivAt P A F hF dF ζ hv z
  rw [magneticGaussianAverageDifferentialTwo_eq_pair P A F hF hG,
    magneticGaussianTimeTwo_eq_generator P A F hF hG dF ζ hv,
    magneticGaussianGeneratorTwo_eq P A F hF hG,
    magneticGaussianSpaceTwo_eq P A F hF] at hd
  exact hd

lemma magneticGaussianSpace_eq (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (ζ v z : ℝ) :
    magneticGaussianSpace ζ v F P.value A.value A.first z =
      fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z := by
  exact magneticGaussianSpaceTwo_eq P A.toTwoJet F hF ζ v z

lemma magneticGaussianGenerator_eq (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (ζ v z : ℝ) :
    magneticGaussianGenerator ζ v F P.value P.first A.value A.first A.second z =
      magneticContinuationSecond ζ (Real.toNNReal v) F P.value P.first
          A.value A.first A.second z / 2 +
        ζ * fieldSpinTransition ζ (Real.toNNReal v) F P.value z *
          fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z := by
  exact magneticGaussianGeneratorTwo_eq P A.toTwoJet F hF hG ζ v z

theorem magneticGaussianAverage_hasFDerivAt_generator (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.value q.2)
      (pairLinear
        (magneticContinuationSecond ζ (Real.toNNReal v) F P.value P.first
            A.value A.first A.second z / 2 +
          ζ * fieldSpinTransition ζ (Real.toNNReal v) F P.value z *
            fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z)
        (fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z)) (v, z) := by
  exact magneticGaussianAverageTwo_hasFDerivAt_generator P A.toTwoJet F hF hG dF ζ hv z

end InvariantIsing

end

end OAI
