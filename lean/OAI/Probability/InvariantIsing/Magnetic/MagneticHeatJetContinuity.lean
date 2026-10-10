import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatSecond
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatContinuity

namespace OAI

/-! Joint continuity of the actual first and second spatial derivatives
of the finite Gaussian continuation, including zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma continuous_magneticGaussianTest {F B : ℝ → ℝ}
    (hF : Continuous F) (hG : HasLinearGrowth F) (hB : Continuous B)
    (bB : MagneticContinuationBound B) (ζ : ℝ) :
    Continuous (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F B q.2) := by
  obtain ⟨C, L, hC, hL, bF⟩ := hG
  obtain ⟨M, hM, bM⟩ := bB
  exact continuous_field_gaussian_tilt_average
    (hF.comp continuous_snd) (hB.comp continuous_snd) continuous_fst continuous_snd
    hC hL hM (fun _ z => by simpa only [Real.norm_eq_abs] using bF z) (fun _ z => bM z) ζ

lemma continuous_magneticHeatSpatial (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatSpatial P A F ζ) := by
  have hA1 : Continuous A.first := continuous_iff_continuousAt.mpr
    fun z => (A.dFirst z).continuousAt
  exact (continuous_magneticGaussianTest hF hG hA1 A.bFirst ζ).add
    (((continuous_magneticHeatMean (A.mul P) F hF hG ζ).sub
      ((continuous_magneticHeatMean A F hF hG ζ).mul
        (continuous_magneticHeatMean P F hF hG ζ))).const_mul ζ)

lemma continuous_magneticHeatSecond (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatSecond P A F ζ) := by
  exact (continuous_magneticHeatSpatial P A.slope F hF hG ζ).add
    (((continuous_magneticHeatSpatial P (A.toMagneticContinuationJet.mul P) F hF hG ζ).sub
      (((continuous_magneticHeatSpatial P A.toMagneticContinuationJet F hF hG ζ).mul
        (continuous_magneticHeatMean P F hF hG ζ)).add
          ((continuous_magneticHeatMean A.toMagneticContinuationJet F hF hG ζ).mul
            (continuous_magneticHeatSpatial P P F hF hG ζ)))).const_mul ζ)

end InvariantIsing

end

end OAI
