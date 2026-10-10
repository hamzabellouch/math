import OAI.Probability.InvariantIsing.Gaussian.GaussianTiltLinearGrowth
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace OAI

/-! Exact conditional relative entropy of two finite exponential tilts.
The resulting one-step budget retains the inverse exponent weight. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron InformationTheory

namespace InvariantIsing

lemma tilted_pair_log_likelihood {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ) (b : ℝ)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ) :
    llr (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)) =ᵐ[μ.tilted (fun x => b * G x)]
      (fun x => b * (G x - F x) +
        Real.log (∫ y, Real.exp (b * F y) ∂μ) - Real.log (∫ y, Real.exp (b * G y) ∂μ)) := by
  have hμG := tilted_absolutelyContinuous μ (fun x => b * G x)
  have hself := hμG.ae_le (log_rnDeriv_tilted_left_self hG)
  have hr := llr_tilted_right hμG hF
  filter_upwards [hself, hr] with x hx hx'
  change llr (μ.tilted (fun x => b * G x)) μ x = _ at hx
  rw [hx] at hx'
  rw [hx']
  ring

theorem tilted_pair_entropy_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ) {b : ℝ} (hb : 0 < b)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hFG : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * G x))) :
    klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)) ≠ ⊤ ∧
      (klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x))).toReal +
        b * (∫ x, F x - G x ∂μ.tilted (fun x => b * G x)) =
        b * (logMean b μ F - logMean b μ G) := by
  let ν := μ.tilted (fun x => b * G x)
  let π := μ.tilted (fun x => b * F x)
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hG
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted hF
  let c := Real.log (∫ y, Real.exp (b * F y) ∂μ) - Real.log (∫ y, Real.exp (b * G y) ∂μ)
  have hac : ν ≪ π := (tilted_absolutelyContinuous μ _).trans (absolutelyContinuous_tilted hF)
  have hr : llr ν π =ᵐ[ν] (fun x => -b * (F x - G x) + c) := by
    filter_upwards [tilted_pair_log_likelihood μ F G b hF hG] with x hx
    rw [hx]
    dsimp only [c]
    ring
  have hI : Integrable (fun x => -b * (F x - G x) + c) ν :=
    (hFG.const_mul (-b)).add (integrable_const c)
  have hi : Integrable (llr ν π) ν := hI.congr hr.symm
  refine ⟨klDiv_ne_top hac hi, ?_⟩
  have he : (klDiv ν π).toReal = ∫ x, llr ν π x ∂ν := by
    rw [toReal_klDiv hac hi]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right]
  have hlin := integral_add (hFG.const_mul (-b)) (integrable_const c)
  have hK : (klDiv ν π).toReal = -b * (∫ x, F x - G x ∂ν) + c := by
    rw [he, integral_congr_ae hr, hlin, integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rfl
  change (klDiv ν π).toReal + b * (∫ x, F x - G x ∂ν) = _
  rw [hK]
  change _ = b * (Real.log (∫ x, Real.exp (b * F x) ∂μ) / b -
    Real.log (∫ x, Real.exp (b * G x) ∂μ) / b)
  dsimp only [c]
  field_simp
  ring

theorem tilted_pair_entropy_budget {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hFG : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * G x))) :
    (klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x))).toReal +
      (∫ x, F x - G x ∂μ.tilted (fun x => b * G x)) ≤ logMean b μ F - logMean b μ G := by
  have he := (tilted_pair_entropy_identity μ F G hb hF hG hFG).2
  have hK := ENNReal.toReal_nonneg (a := klDiv
    (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)))
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hK]

end InvariantIsing

end

end OAI
