import OAI.Probability.InvariantIsing.Fields.FieldScalarSecondDerivative

namespace OAI

/-! Bounded first and second spatial derivatives for the scalar Ising
backward recursion, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_hasDerivAt_tanh (z : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh z) ^ 2) z := by
  have h := (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne'
  have hrel := Real.cosh_sq_sub_sinh_sq z
  convert h using 1
  · funext x
    exact Real.tanh_eq_sinh_div_cosh x
  · rw [← pow_two, ← pow_two, hrel]

lemma field_tanh_second_bound (z : ℝ) : |1 / (Real.cosh z) ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (Real.cosh z) ^ 2)]
  apply (div_le_one (sq_pos_of_pos (Real.cosh_pos z))).mpr
  nlinarith [Real.one_le_cosh z]

theorem fieldScalarLogCoshSecond_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    Measurable (fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
      (fun x => 1 / (Real.cosh x) ^ 2)) ∧
      ∀ z, |fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z| ≤ fieldScalarSecondCap L 1 1 := by
  have ht : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply fieldScalarSecond_regular L hL measurable_logCosh logCosh_linearGrowth
    ht
    (by fun_prop) zero_le_one field_abs_tanh_le_one field_tanh_second_bound

theorem hasDerivAt_fieldScalarLogCoshMean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh)
      (fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z) z := by
  have ht : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply hasDerivAt_fieldScalarMean L hL measurable_logCosh logCosh_linearGrowth ht
    (by fun_prop) zero_le_one field_abs_tanh_le_one field_tanh_second_bound
  · intro x
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  · exact field_hasDerivAt_tanh

end InvariantIsing

end

end OAI
