import OAI.Probability.InvariantIsing.Magnetic.MagneticJetProduct
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatMean

namespace OAI

/-! The mixed derivative of the first spatial derivative of a bounded
finite Gaussian continuation. The proof differentiates actual normalized
averages and identifies coefficients by ordinary derivative uniqueness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatSpatial (P A : MagneticContinuationJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage q.1 ζ F A.first q.2 + ζ *
    (magneticHeatMean (A.mul P) F ζ q - magneticHeatMean A F ζ q * magneticHeatMean P F ζ q)

lemma magneticHeatSpatial_eq (P A : MagneticContinuationJet) (F : ℝ → ℝ)
    (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatSpatial P A F ζ q =
      fieldTiltSpatial ζ (Real.toNNReal q.1) F P.value A.value A.first q.2 := by
  unfold magneticHeatSpatial fieldTiltSpatial
  rw [magneticHeatMean_eq _ _ hF, magneticHeatMean_eq _ _ hF, magneticHeatMean_eq _ _ hF]
  rw [field_gaussianTiltAverage_eq_transition q.1 ζ hF A.mFirst]
  rfl

theorem magneticHeatSpatial_hasFDerivAt (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    let K := A.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatSpatial P A F ζ)
      (pairLinear (K.third z / 2 + ζ * (J.value z * K.second z + J.first z * K.first z))
        (K.second z)) (v, z) := by
  let w := Real.toNNReal v
  let J := P.transition P ζ w F hF hG dF
  let K := A.transition P ζ w F hF hG dF
  let U := fieldSpinTransition ζ w F A.first
  let V := fieldSpinTransition ζ w F (A.mul P).value
  let U1 := fieldTiltSpatial ζ w F P.value A.first A.second
  let V1 := fieldTiltSpatial ζ w F P.value (A.mul P).value (A.mul P).first
  let U2 := magneticContinuationSecond ζ w F P.value P.first A.first A.second A.third
  let V2 := magneticContinuationSecond ζ w F P.value P.first
    (A.mul P).value (A.mul P).first (A.mul P).second
  have hU (x : ℝ) : HasDerivAt U (U1 x) x :=
    magneticTwoJet_average_hasDerivAt P A.slopeTwoJet F hF hG dF ζ w x
  have hV (x : ℝ) : HasDerivAt V (V1 x) x :=
    ((A.mul P).transition P ζ w F hF hG dF).dValue x
  have hU1 (x : ℝ) : HasDerivAt U1 (U2 x) x :=
    magneticTwoJet_spatial_hasDerivAt P A.slopeTwoJet F hF hG dF ζ w x
  have hV1 (x : ℝ) : HasDerivAt V1 (V2 x) x :=
    ((A.mul P).transition P ζ w F hF hG dF).dFirst x
  have hK : K.first = fun x => U x + ζ * (V x - K.value x * J.value x) := by rfl
  have hr (x : ℝ) : U1 x + ζ * (V1 x - (K.first x * J.value x + K.value x * J.first x)) =
      K.second x := by
    have hd := (hU x).add (((hV x).sub ((K.dValue x).mul (J.dValue x))).const_mul ζ)
    change HasDerivAt (fun y => U y + ζ * (V y - K.value y * J.value y)) _ x at hd
    rw [← hK] at hd
    exact hd.unique (K.dFirst x)
  have hR : (fun x => U1 x + ζ * (V1 x - (K.first x * J.value x + K.value x * J.first x))) =
      K.second := funext hr
  have hs : U2 z + ζ * (V2 z - (K.second z * J.value z +
      2 * K.first z * J.first z + K.value z * J.second z)) = K.third z := by
    have hd := (hU1 z).add (((hV1 z).sub
      (((K.dFirst z).mul (J.dValue z)).add ((K.dValue z).mul (J.dFirst z)))).const_mul ζ)
    have hd' : HasDerivAt
        (fun x => U1 x + ζ * (V1 x - (K.first x * J.value x + K.value x * J.first x)))
        (U2 z + ζ * (V2 z - (K.second z * J.value z +
          2 * K.first z * J.first z + K.value z * J.second z))) z := by
      convert hd using 1
      ring
    rw [hR] at hd'
    exact hd'.unique (K.dSecond z)
  have hA := magneticHeatContinuation_hasFDerivAt P A F hF hG dF ζ hv z
  have hP := magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv z
  have hB := magneticGaussianAverageTwo_hasFDerivAt_generator P A.slopeTwoJet F hF hG dF ζ hv z
  have hC := magneticHeatContinuation_hasFDerivAt P (A.mul P) F hF hG dF ζ hv z
  change HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.first q.2)
    (pairLinear (U2 z / 2 + ζ * J.value z * U1 z) (U1 z)) (v, z) at hB
  change HasFDerivAt (magneticHeatMean (A.mul P) F ζ)
    (pairLinear (V2 z / 2 + ζ * J.value z * V1 z) (V1 z)) (v, z) at hC
  have eA : magneticHeatMean A F ζ (v, z) = K.value z := magneticHeatMean_eq A F hF ζ _
  have eP : magneticHeatMean P F ζ (v, z) = J.value z := magneticHeatMean_eq P F hF ζ _
  have hd := hB.add ((hC.sub (hA.mul hP)).const_mul ζ)
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp only [add_apply, sub_apply, smul_apply, pairLinear_apply, smul_eq_mul, eA, eP]
    have hrz := hr z
    linear_combination -(p.1 / 2) * hs - ζ * J.value z * p.1 * hrz - p.2 * hrz

end InvariantIsing

end

end OAI
