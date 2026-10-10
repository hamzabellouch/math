import OAI.Probability.InvariantIsing.Fields.FieldSpinLinear
import OAI.Probability.InvariantIsing.Fields.FieldScalarLogCoshSecond

namespace OAI

/-! The terminal Ising identity gives the constant term at the last
covariance level of the backward derivative. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_tanh_generator_one (z : ℝ) :
    1 / (Real.cosh z) ^ 2 + (Real.tanh z) ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have h := Real.cosh_sq_sub_sinh_sq z
  field_simp [(Real.cosh_pos z).ne']
  nlinarith

lemma field_tanh_generator (ζ z : ℝ) :
    1 / (Real.cosh z) ^ 2 + ζ * (Real.tanh z) ^ 2 =
      1 + (ζ - 1) * (Real.tanh z) ^ 2 := by
  have h := field_tanh_generator_one z
  nlinarith

lemma fieldSpinTransition_terminal_generator (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    fieldSpinTransition ζ v (fun x => Real.log (Real.cosh x))
      (fun x => 1 / (Real.cosh x) ^ 2 + ζ * (Real.tanh x) ^ 2) z =
      1 + (ζ - 1) * fieldSpinTransition ζ v (fun x => Real.log (Real.cosh x))
        (fun x => (Real.tanh x) ^ 2) z := by
  have ht : Measurable (fun x : ℝ => (Real.tanh x) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hB : ∀ x : ℝ, |(ζ - 1) * (Real.tanh x) ^ 2| ≤ |ζ - 1| := by
    intro x
    rw [abs_mul, abs_pow]
    have hsq : |Real.tanh x| ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (field_abs_tanh_le_one x) 2
    exact (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)).trans_eq (mul_one _)
  have he : (fun x => 1 / (Real.cosh x) ^ 2 + ζ * (Real.tanh x) ^ 2) =
      (fun x => (1 : ℝ) + (ζ - 1) * (Real.tanh x) ^ 2) := by
    funext x
    exact field_tanh_generator ζ x
  have hm : Measurable (fun x : ℝ => (ζ - 1) * (Real.tanh x) ^ 2) :=
    ht.const_mul (ζ - 1)
  rw [he, fieldSpinTransition_add (A := 1) ζ v measurable_logCosh logCosh_linearGrowth
    measurable_const hm (fun _ => by norm_num) hB,
    fieldSpinTransition_const ζ v measurable_logCosh logCosh_linearGrowth,
    fieldSpinTransition_const_mul]

end InvariantIsing

end

end OAI
