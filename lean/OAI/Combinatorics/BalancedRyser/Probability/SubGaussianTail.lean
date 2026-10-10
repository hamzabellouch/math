import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {c : ℝ≥0}

lemma subGaussian_abs_tail [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc
    μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω}) ≤
        μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} := measureReal_union_le _ _
    _ ≤ exp (-u ^ 2 / (2 * c)) + exp (-u ^ 2 / (2 * c)) :=
      add_le_add (h.measure_ge_le hu) (h.neg.measure_ge_le hu)
    _ = _ := by ring

lemma subGaussian_mono_parameter (h : HasSubgaussianMGF X c μ)
    {d : ℝ≥0} (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le θ := (h.mgf_le θ).trans (by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ d from hcd) (sq_nonneg θ))
      (by norm_num))

lemma subGaussian_abs_tail_of_parameter_le [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {v u : ℝ} (hv : 0 ≤ v)
    (hcv : (c : ℝ) ≤ v) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * v)) := by
  exact subGaussian_abs_tail
    (subGaussian_mono_parameter h (d := ⟨v, hv⟩) hcv) hu

lemma subGaussian_abs_tail_horizon [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {t T : ℕ} (htT : t ≤ T)
    {L u : ℝ} (hct : (c : ℝ) ≤ 4 * t * L ^ 2) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (8 * T * L ^ 2)) := by
  have hv : 0 ≤ 4 * (T : ℝ) * L ^ 2 := by positivity
  have hcv : (c : ℝ) ≤ 4 * (T : ℝ) * L ^ 2 := hct.trans (by
    gcongr)
  have hb := subGaussian_abs_tail_of_parameter_le h hv hcv hu
  convert hb using 1
  congr 2
  ring

end Balanced

end OAI
