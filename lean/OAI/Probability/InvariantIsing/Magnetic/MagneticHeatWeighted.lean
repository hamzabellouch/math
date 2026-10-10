import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatSecond
import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatInverse

namespace OAI

/-! The actual drift-free equation for q²Hᵤᵤ along the inverse mean.
All time derivatives come from normalized Gaussian averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal Topology

namespace InvariantIsing

def magneticHeatWeighted (P A : MagneticContinuationFourJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  magneticHeatSecond P.toMagneticContinuationJet A F ζ q -
    magneticHeatSpatial P.toMagneticContinuationJet A.toMagneticContinuationJet F ζ q *
      magneticHeatSecond P.toMagneticContinuationJet P F ζ q / magneticHeatCurvature P.toMagneticContinuationJet F ζ q

lemma magneticHeatWeighted_eq (P A : MagneticContinuationFourJet) (F : ℝ → ℝ)
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatWeighted P A F ζ q =
      magneticWeightedJetValue
        (P.transition P.toMagneticContinuationJet ζ (Real.toNNReal q.1) F hF hG dF)
        (A.transition P.toMagneticContinuationJet ζ (Real.toNNReal q.1) F hF hG dF) q.2 := by
  unfold magneticHeatWeighted magneticWeightedJetValue
  rw [magneticHeatSecond_eq _ _ F hF, magneticHeatSecond_eq _ _ F hF,
    magneticHeatSpatial_eq _ _ F hF, magneticHeatCurvature_eq _ F hF]
  simp only [MagneticContinuationFourJet.transition, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two]

theorem magneticHeatWeighted_inverse_hasDerivAt (P A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v s : ℝ} (hv : 0 < v)
    {b : ℝ → ℝ} (hb : ContinuousAt b v)
    (he : ∀ᶠ t in 𝓝 v, magneticHeatMean P.toMagneticContinuationJet F ζ (t, b t) = s)
    (hq : (P.toMagneticContinuationJet.transition P.toMagneticContinuationJet ζ
      (Real.toNNReal v) F hF hG dF).first (b v) ≠ 0) :
    let J := P.transition P.toMagneticContinuationJet ζ (Real.toNNReal v) F hF hG dF
    let K := A.transition P.toMagneticContinuationJet ζ (Real.toNNReal v) F hF hG dF
    HasDerivAt (fun t => magneticHeatWeighted P A F ζ (t, b t))
      ((J.first (b v)) ^ 2 / 2 * magneticWeightedInverseSecond J K (b v) +
        (J.third (b v) / J.first (b v) - (J.second (b v)) ^ 2 / (J.first (b v)) ^ 2 +
          2 * ζ * J.first (b v)) * magneticWeightedJetValue J K (b v)) v := by
  let w := Real.toNNReal v
  let J := P.transition P.toMagneticContinuationJet ζ w F hF hG dF
  let K := A.transition P.toMagneticContinuationJet ζ w F hF hG dF
  let q := J.first (b v)
  let r := J.second (b v)
  let d := J.third (b v)
  let e := J.fourth (b v)
  change q ≠ 0 at hq
  have hm := magneticHeatMean_hasFDerivAt P.toMagneticContinuationJet F hF hG dF ζ hv (b v)
  have hc := inverse_mean_curvature_variation hb hq hm he
    (magneticHeatCurvature_hasFDerivAt P.toMagneticContinuationJet F hF hG dF ζ hv (b v))
  have hr := inverse_mean_curvature_variation hb hq hm he
    (magneticHeatSecond_hasFDerivAt P.toMagneticContinuationJet P F hF hG dF ζ hv (b v))
  have hk1 := inverse_mean_curvature_variation hb hq hm he
    (magneticHeatSpatial_hasFDerivAt P.toMagneticContinuationJet A.toMagneticContinuationJet F hF hG dF ζ hv (b v))
  have hk2 := inverse_mean_curvature_variation hb hq hm he
    (magneticHeatSecond_hasFDerivAt P.toMagneticContinuationJet A F hF hG dF ζ hv (b v))
  have eqc : magneticHeatCurvature P.toMagneticContinuationJet F ζ (v, b v) = q := by
    rw [magneticHeatCurvature_eq _ F hF]
    simp only [q, J, w, MagneticContinuationFourJet.transition, MagneticContinuationJet.transition,
      fieldCurvatureTransform, fieldTiltSpatial, pow_two]
  have eqr : magneticHeatSecond P.toMagneticContinuationJet P F ζ (v, b v) = r :=
    magneticHeatSecond_eq _ _ F hF ζ _
  have eqk1 : magneticHeatSpatial P.toMagneticContinuationJet A.toMagneticContinuationJet F ζ
      (v, b v) = K.first (b v) := magneticHeatSpatial_eq _ _ F hF ζ _
  have hc' : HasDerivAt (fun t => magneticHeatCurvature P.toMagneticContinuationJet F ζ (t, b t))
      (d / 2 - r ^ 2 / (2 * q) + ζ * q ^ 2) v := by
    change HasDerivAt _ (d / 2 + ζ * (q ^ 2 + J.value (b v) * r) -
      r * (r / 2 + ζ * J.value (b v) * q) / q) v at hc
    convert hc using 1
    field_simp [hq]
    ring
  have hr' : HasDerivAt (fun t => magneticHeatSecond P.toMagneticContinuationJet P F ζ (t, b t))
      (e / 2 - r * d / (2 * q) + 3 * ζ * q * r) v := by
    change HasDerivAt _ (e / 2 + ζ * (J.value (b v) * d + 2 * q * r + r * q) -
      d * (r / 2 + ζ * J.value (b v) * q) / q) v at hr
    convert hr using 1
    field_simp [hq]
    ring
  have hk1' : HasDerivAt
      (fun t => magneticHeatSpatial P.toMagneticContinuationJet A.toMagneticContinuationJet F ζ (t, b t))
      (K.third (b v) / 2 - r * K.second (b v) / (2 * q) + ζ * q * K.first (b v)) v := by
    change HasDerivAt _ (K.third (b v) / 2 +
      ζ * (J.value (b v) * K.second (b v) + q * K.first (b v)) -
      K.second (b v) * (r / 2 + ζ * J.value (b v) * q) / q) v at hk1
    convert hk1 using 1
    field_simp [hq]
    ring
  have hk2' : HasDerivAt (fun t => magneticHeatSecond P.toMagneticContinuationJet A F ζ (t, b t))
      (K.fourth (b v) / 2 - r * K.third (b v) / (2 * q) +
        2 * ζ * q * K.second (b v) + ζ * r * K.first (b v)) v := by
    change HasDerivAt _ (K.fourth (b v) / 2 +
      ζ * (J.value (b v) * K.third (b v) + 2 * q * K.second (b v) + r * K.first (b v)) -
      K.third (b v) * (r / 2 + ζ * J.value (b v) * q) / q) v at hk2
    convert hk2 using 1
    field_simp [hq]
    ring
  have hd := hk2'.sub ((hk1'.mul hr').div hc' (eqc.symm ▸ hq))
  convert hd using 1
  · rfl
  · simp only [Pi.mul_apply]
    rw [eqk1, eqr, eqc]
    change q ^ 2 / 2 *
        ((K.fourth (b v) - K.third (b v) * r / q - 2 * K.second (b v) * d / q +
          2 * K.second (b v) * r ^ 2 / q ^ 2 - K.first (b v) * e / q +
          3 * K.first (b v) * r * d / q ^ 2 - 2 * K.first (b v) * r ^ 3 / q ^ 3) / q ^ 2 -
          (K.third (b v) - (K.second (b v) * r + K.first (b v) * d) / q +
            K.first (b v) * r ^ 2 / q ^ 2) * r / q ^ 3) +
        (d / q - r ^ 2 / q ^ 2 + 2 * ζ * q) *
          (K.second (b v) - K.first (b v) * r / q) = _
    field_simp [hq]
    ring

end InvariantIsing

end

end OAI
