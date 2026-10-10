import OAI.Probability.InvariantIsing.Magnetic.MagneticFourJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatSpatial

namespace OAI

/-! Joint variance/spatial differentiation of the second spatial
derivative. Fourth terminal derivatives suffice; no unproved interchange
of differentiation and Gaussian integration is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatSecond (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  magneticHeatSpatial P A.slope F ζ q + ζ *
    (magneticHeatSpatial P (A.toMagneticContinuationJet.mul P) F ζ q -
      (magneticHeatSpatial P A.toMagneticContinuationJet F ζ q * magneticHeatMean P F ζ q +
        magneticHeatMean A.toMagneticContinuationJet F ζ q * magneticHeatSpatial P P F ζ q))

lemma magneticHeatSecond_eq (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatSecond P A F ζ q = magneticContinuationSecond ζ (Real.toNNReal q.1)
      F P.value P.first A.value A.first A.second q.2 := by
  unfold magneticHeatSecond
  simp only [magneticHeatSpatial_eq _ _ F hF, magneticHeatMean_eq _ F hF]
  rfl

theorem magneticHeatSecond_hasFDerivAt (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    let K := A.toMagneticContinuationJet.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatSecond P A F ζ)
      (pairLinear (A.transitionFourth P ζ (Real.toNNReal v) F hF hG dF z / 2 +
        ζ * (J.value z * K.third z + 2 * J.first z * K.second z + J.second z * K.first z))
        (K.third z)) (v, z) := by
  let w := Real.toNNReal v
  let J := P.transition P ζ w F hF hG dF
  let K := A.toMagneticContinuationJet.transition P ζ w F hF hG dF
  let R := A.slope.transition P ζ w F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ w F hF hG dF
  have h2 : R.first z + ζ * (W.first z -
      (K.first z * J.value z + K.value z * J.first z)) = K.second z := by rfl
  have h3 : R.second z + ζ * (W.second z -
      (K.second z * J.value z + 2 * K.first z * J.first z + K.value z * J.second z)) =
      K.third z := by
    exact (congrFun (A.transition_third_eq P ζ w F hF hG dF) z).symm
  have h4 : A.transitionFourth P ζ w F hF hG dF z = R.third z + ζ *
      (W.third z - (K.third z * J.value z + 3 * K.second z * J.first z +
        3 * K.first z * J.second z + K.value z * J.third z)) := by rfl
  have hR := magneticHeatSpatial_hasFDerivAt P A.slope F hF hG dF ζ hv z
  have hW := magneticHeatSpatial_hasFDerivAt P (A.toMagneticContinuationJet.mul P) F hF hG dF ζ hv z
  have hK := magneticHeatSpatial_hasFDerivAt P A.toMagneticContinuationJet F hF hG dF ζ hv z
  have hJ := magneticHeatSpatial_hasFDerivAt P P F hF hG dF ζ hv z
  have hA := magneticHeatContinuation_hasFDerivAt P A.toMagneticContinuationJet F hF hG dF ζ hv z
  have hP := magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv z
  have eK : magneticHeatSpatial P A.toMagneticContinuationJet F ζ (v, z) = K.first z :=
    magneticHeatSpatial_eq P A.toMagneticContinuationJet F hF ζ _
  have eJ : magneticHeatSpatial P P F ζ (v, z) = J.first z := magneticHeatSpatial_eq P P F hF ζ _
  have eA : magneticHeatMean A.toMagneticContinuationJet F ζ (v, z) = K.value z :=
    magneticHeatMean_eq A.toMagneticContinuationJet F hF ζ _
  have eP : magneticHeatMean P F ζ (v, z) = J.value z := magneticHeatMean_eq P F hF ζ _
  have hd := hR.add ((hW.sub ((hK.mul hP).add (hA.mul hJ))).const_mul ζ)
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp only [add_apply, sub_apply, smul_apply, pairLinear_apply, smul_eq_mul, eK, eJ, eA, eP]
    dsimp only [J, K, R, W, w] at h2 h3 h4
    linear_combination (p.1 / 2) * h4 - (ζ * J.value z * p.1 + p.2) * h3 -
      ζ * J.first z * p.1 * h2

end InvariantIsing

end

end OAI
