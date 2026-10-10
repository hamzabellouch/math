import OAI.Probability.InvariantIsing.Core.TiltedRelativeEntropy
import Mathlib.Probability.Moments.SubGaussian

namespace OAI

/-! Relative entropy controls the expectation of a canonical
sub-Gaussian observable. This avoids a loss from the ambient dimension. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal

namespace InvariantIsing

theorem entropy_variational_mean {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) (F : X → ℝ)
    (hF : Integrable F μ) (he : Integrable (fun x => Real.exp (F x)) ν) :
    (∫ x, F x ∂μ) ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (F x) ∂ν) := by
  let π := ν.tilted F
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted he
  have hac' : μ ≪ π := hac.trans (absolutelyContinuous_tilted he)
  have hi : Integrable (llr μ π) μ := integrable_llr_tilted_right hac hF hllr he
  have hn := integral_llr_add_sub_measure_univ_nonneg hac' hi
  have hE := integral_llr_tilted_right hac hF he hllr
  have hK := toReal_klDiv hac hllr
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right] at hn hK
  change 0 ≤ ∫ x, llr μ (ν.tilted F) x ∂μ at hn
  linarith

theorem entropy_subgaussian_mean {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) (Y : X → ℝ) {c : ℝ≥0}
    (hY : Integrable Y μ) (hG : HasSubgaussianMGF Y c ν) {t : ℝ} (ht : 0 < t) :
    |∫ x, Y x ∂μ| ≤ (klDiv μ ν).toReal / t + c * t / 2 := by
  have hp := entropy_variational_mean μ ν hac hllr (fun x => t * Y x)
    (hY.const_mul t) (hG.integrable_exp_mul t)
  have hn := entropy_variational_mean μ ν hac hllr (fun x => -t * Y x)
    (hY.const_mul (-t)) (hG.integrable_exp_mul (-t))
  have hgp := hG.cgf_le t
  have hgn := hG.cgf_le (-t)
  change Real.log (∫ x, Real.exp (t * Y x) ∂ν) ≤ _ at hgp
  change Real.log (∫ x, Real.exp (-t * Y x) ∂ν) ≤ _ at hgn
  rw [integral_const_mul] at hp hn
  have hbound : t * |∫ x, Y x ∂μ| ≤ (klDiv μ ν).toReal + c * t ^ 2 / 2 := by
    have h := (abs_le.mpr (show -( (klDiv μ ν).toReal + c * t ^ 2 / 2) ≤
      t * (∫ x, Y x ∂μ) ∧ t * (∫ x, Y x ∂μ) ≤
        (klDiv μ ν).toReal + c * t ^ 2 / 2 by constructor <;> nlinarith))
    simpa only [abs_mul, abs_of_pos ht] using h
  apply (mul_le_mul_iff_right₀ ht).mp
  calc
    _ = t * |∫ x, Y x ∂μ| := by ring
    _ ≤ _ := hbound
    _ = t * ((klDiv μ ν).toReal / t + c * t / 2) := by field_simp

end InvariantIsing

end

end OAI
