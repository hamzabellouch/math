import OAI.Probability.InvariantIsing.Magnetic.MagneticTwoJetSpatial

namespace OAI

/-! The actual scalar curvature satisfies the differentiated heat equation.
The computation uses only four derivatives of the finite scalar value. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatCurvature (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage q.1 ζ F P.first q.2 + ζ *
    (gaussianTiltAverage q.1 ζ F (fun y => (P.value y) ^ 2) q.2 -
      (gaussianTiltAverage q.1 ζ F P.value q.2) ^ 2)

lemma magneticHeatCurvature_eq (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatCurvature P F ζ q =
      fieldCurvatureTransform ζ (Real.toNNReal q.1) F P.value P.first q.2 := by
  unfold magneticHeatCurvature fieldCurvatureTransform
  rw [field_gaussianTiltAverage_eq_transition q.1 ζ hF P.mFirst,
    field_gaussianTiltAverage_eq_transition q.1 ζ (a := fun y => (P.value y) ^ 2)
      hF (P.mValue.pow_const 2),
    field_gaussianTiltAverage_eq_transition q.1 ζ hF P.mValue]

theorem magneticHeatCurvature_hasFDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatCurvature P F ζ)
      (pairLinear (J.third z / 2 + ζ * ((J.first z) ^ 2 + J.value z * J.second z))
        (J.second z)) (v, z) := by
  let w := Real.toNNReal v
  let J := P.transition P ζ w F hF hG dF
  let U := fieldSpinTransition ζ w F P.first
  let V := fieldSpinTransition ζ w F P.square.value
  let U1 := fieldTiltSpatial ζ w F P.value P.first P.second
  let V1 := fieldTiltSpatial ζ w F P.value P.square.value P.square.first
  let U2 := magneticContinuationSecond ζ w F P.value P.first P.first P.second P.third
  let V2 := magneticContinuationSecond ζ w F P.value P.first
    P.square.value P.square.first P.square.second
  have hU (x : ℝ) : HasDerivAt U (U1 x) x :=
    magneticTwoJet_average_hasDerivAt P P.slopeTwoJet F hF hG dF ζ w x
  have hV (x : ℝ) : HasDerivAt V (V1 x) x :=
    magneticTwoJet_average_hasDerivAt P P.square.toTwoJet F hF hG dF ζ w x
  have hU1 (x : ℝ) : HasDerivAt U1 (U2 x) x :=
    magneticTwoJet_spatial_hasDerivAt P P.slopeTwoJet F hF hG dF ζ w x
  have hV1 (x : ℝ) : HasDerivAt V1 (V2 x) x :=
    magneticTwoJet_spatial_hasDerivAt P P.square.toTwoJet F hF hG dF ζ w x
  have hJ : J.first = fun x => U x + ζ * (V x - (J.value x) ^ 2) := by
    funext x
    dsimp only [J, MagneticContinuationJet.transition, fieldTiltSpatial, U, V,
      MagneticContinuationJet.square]
    simp only [pow_two]
  have hr (x : ℝ) : U1 x + ζ * (V1 x - 2 * J.value x * J.first x) = J.second x := by
    have hd := (hU x).add (((hV x).sub ((J.dValue x).pow 2)).const_mul ζ)
    change HasDerivAt (fun y => U y + ζ * (V y - (J.value y) ^ 2))
      (U1 x + ζ * (V1 x - (2 : ℝ) * J.value x ^ (2 - 1) * J.first x)) x at hd
    rw [← hJ] at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.unique (J.dFirst x)
  have hR : (fun x => U1 x + ζ * (V1 x - 2 * J.value x * J.first x)) = J.second :=
    funext hr
  have hs : U2 z + ζ * (V2 z - 2 * (J.first z) ^ 2 -
      2 * J.value z * J.second z) = J.third z := by
    have hd := (hU1 z).add (((hV1 z).sub
      (((J.dValue z).mul (J.dFirst z)).const_mul 2)).const_mul ζ)
    have hd' : HasDerivAt
        (fun x => U1 x + ζ * (V1 x - 2 * J.value x * J.first x))
        (U2 z + ζ * (V2 z - 2 * (J.first z) ^ 2 -
          2 * J.value z * J.second z)) z := by
      convert hd using 1
      · funext x
        dsimp
        ring
      · ring
    rw [hR] at hd'
    exact hd'.unique (J.dSecond z)
  have hM := magneticGaussianAverageTwo_hasFDerivAt_generator P P.toTwoJet F hF hG dF ζ hv z
  have hQ := magneticGaussianAverageTwo_hasFDerivAt_generator P P.slopeTwoJet F hF hG dF ζ hv z
  have hS := magneticGaussianAverageTwo_hasFDerivAt_generator P P.square.toTwoJet F hF hG dF ζ hv z
  change HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F P.value q.2)
    (pairLinear (J.second z / 2 + ζ * J.value z * J.first z) (J.first z)) (v, z) at hM
  change HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F P.first q.2)
    (pairLinear (U2 z / 2 + ζ * J.value z * U1 z) (U1 z)) (v, z) at hQ
  change HasFDerivAt (fun q : ℝ × ℝ =>
      gaussianTiltAverage q.1 ζ F (fun y => (P.value y) ^ 2) q.2)
    (pairLinear (V2 z / 2 + ζ * J.value z * V1 z) (V1 z)) (v, z) at hS
  have hm : gaussianTiltAverage v ζ F P.value z = J.value z :=
    congrFun (field_gaussianTiltAverage_eq_transition v ζ hF P.mValue) z
  have hd := hQ.add ((hS.sub (hM.pow 2)).const_mul ζ)
  change HasFDerivAt (magneticHeatCurvature P F ζ)
    (pairLinear (J.third z / 2 + ζ * ((J.first z) ^ 2 + J.value z * J.second z))
      (J.second z)) (v, z)
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp only [add_apply, sub_apply, smul_apply, pairLinear_apply, smul_eq_mul]
    simp only [hm]
    have hrz := hr z
    linear_combination -(p.1 / 2) * hs - ζ * J.value z * p.1 * hrz - p.2 * hrz

end InvariantIsing

end

end OAI
