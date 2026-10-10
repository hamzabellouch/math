import OAI.Probability.SpanningForest.WeightedInnovation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem336.Innovation

theorem gaussian_error_le_smallStep {h L c m : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hL : 0 ≤ L) :
    16 * ((Real.sqrt (h * c)) ^ 3 * m + (h * L) ^ 3) +
        (2 * (h * L) * Real.sqrt (h * c) + (h * L) ^ 2) / 2 +
        (h * c / 2) ^ 2 ≤
      (16 * ((Real.sqrt c) ^ 3 * m + L ^ 3) + L * Real.sqrt c +
        L ^ 2 / 2 + c ^ 2 / 4) * h * Real.sqrt h := by
  have hs0 := Real.sqrt_nonneg h
  have hs1 : Real.sqrt h ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hh1
  have hs2 := Real.sq_sqrt hh0
  have hh_s : h ≤ Real.sqrt h := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hh2 : h ^ 2 ≤ h * Real.sqrt h := by
    nlinarith [mul_le_mul_of_nonneg_left hh_s hh0]
  have hh3 : h ^ 3 ≤ h * Real.sqrt h := by
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
  have hs3 : (Real.sqrt h) ^ 3 = h * Real.sqrt h := by nlinarith
  rw [Real.sqrt_mul hh0, mul_pow, hs3]
  have hL3 := mul_le_mul_of_nonneg_right hh3 (pow_nonneg hL 3)
  have hL2 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg L)
  have hc2 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg c)
  nlinarith [hL3, hL2, hc2]

def gaussianErrorConstant (L c : ℝ) : ℝ :=
  16 * ((Real.sqrt c) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂gaussianReal 0 1) + L ^ 3) +
    L * Real.sqrt c + L ^ 2 / 2 + c ^ 2 / 4

lemma gaussianErrorConstant_nonneg {L c : ℝ} (hL : 0 ≤ L) :
    0 ≤ gaussianErrorConstant L c := by
  have hm : 0 ≤ ∫ z : ℝ, |z| ^ 3 ∂gaussianReal 0 1 :=
    integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  unfold gaussianErrorConstant
  positivity

theorem gaussian_smallStep_characteristic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Q R : Ω → ℝ} {K : Ω → ℂ} {h L c : ℝ} {v : ℝ≥0}
    (hLaw : HasLaw Q (gaussianReal 0 v) P) (hIndep : IndepFun K Q P)
    (hR : AEStronglyMeasurable R P)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hL : 0 ≤ L)
    (hvariance : (v : ℝ) = h * c) (hsmall : h * c ≤ 2)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ h * L)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hmean : (∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ∂P) = 0) :
    ‖(∫ ω, K ω * Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (Real.exp (-(h * c / 2)) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      gaussianErrorConstant L c * h * Real.sqrt h := by
  have hv : (v : ℝ) ≤ 2 := by simpa only [hvariance] using hsmall
  have hbase := gaussian_bounded_perturbation_characteristic hLaw hIndep hR
    (mul_nonneg hh0 hL) hRbound hKmeas hK hmean hv
  rw [hvariance] at hbase
  exact hbase.trans (gaussian_error_le_smallStep hh0 hh1 hL)

end Problem336.Innovation

end

end OAI
