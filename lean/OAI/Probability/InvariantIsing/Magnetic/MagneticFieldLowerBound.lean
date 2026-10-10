import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldBias
import OAI.Probability.InvariantIsing.Fields.FieldMajorantGaussian

namespace OAI

/-! Linear bias coercivity for the finite magnetic field functional.
The lower estimate is preserved by the actual Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma affine_le_gaussianOperator {F : ℝ → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {a : ℝ} (ha : 0 ≤ a) (v : ℝ≥0)
    (m c : ℝ) (hl : ∀ z, m * z + c ≤ F z) (z : ℝ) :
    m * z + c ≤ gaussianOperator a v F z := by
  have hi : Integrable (fun u : ℝ => u) (gaussianReal z v) := IsGaussian.integrable_id
  have hmean : m * z + c ≤ ∫ u, F u ∂gaussianReal z v := by
    calc
      _ = ∫ u, m * u + c ∂gaussianReal z v := by
        rw [integral_add (hi.const_mul m) (integrable_const c),
          integral_const_mul, integral_id_gaussianReal, integral_const]
        simp
      _ ≤ _ := integral_mono ((hi.const_mul m).add (integrable_const c))
        (field_gaussian_linear_integrable v z hF hG) hl
  by_cases ha0 : a = 0
  · subst a
    rwa [gaussianOperator_eq_gaussian_integral v hF]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [gaussianOperator_eq_gaussian_exp_integral ha0 v hF]
    exact hmean.trans (mean_le_log_moment_div (gaussianReal z v)
      (field_gaussian_linear_integrable v z hF hG) hap
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG a))

lemma affine_le_fieldScalarValue (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (m c : ℝ) (hl : ∀ z, m * z + c ≤ F z) (z : ℝ) :
    m * z + c ≤ fieldScalarValue L F z := by
  induction L generalizing z with
  | nil => exact hl z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htail := fieldScalarValue_regular L ht hF hG
    exact affine_le_gaussianOperator htail.1 htail.2 (hL av (List.mem_cons_self)).le
      av.2 m c (ih ht) z

lemma signed_bias_le_logcosh (b : ℝ) :
    b - Real.log 2 ≤ Real.log (Real.cosh b) := by
  have he : Real.exp b ≤ 2 * Real.cosh b := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-b)]
  have hl := Real.log_le_log (Real.exp_pos b) he
  rw [Real.log_exp, Real.log_mul (by norm_num) (Real.cosh_pos b).ne'] at hl
  linarith

lemma fieldValue_bias_lower (h : FieldStep) (b : ℝ) :
    |b| - Real.log 2 - h.height (Fin.last h.depth) / 2 ≤ fieldValue h b := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hplus : ∀ z, (1 : ℝ) * z + -Real.log 2 ≤
      fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) z := by
    apply affine_le_fieldScalarValue _ hL measurable_logCosh logCosh_linearGrowth
    intro z
    simpa only [one_mul, sub_eq_add_neg] using signed_bias_le_logcosh z
  have hminus : ∀ z, (-1 : ℝ) * z + -Real.log 2 ≤
      fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) z := by
    apply affine_le_fieldScalarValue _ hL measurable_logCosh logCosh_linearGrowth
    intro z
    simpa only [Real.cosh_neg, neg_mul, one_mul, sub_eq_add_neg]
      using signed_bias_le_logcosh (-z)
  have hp := affine_le_gaussianOperator hF.1 hF.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0)) 1 (-Real.log 2) hplus b
  have hm := affine_le_gaussianOperator hF.1 hF.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0)) (-1) (-Real.log 2) hminus b
  change 1 * b + -Real.log 2 ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hp
  change -1 * b + -Real.log 2 ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hm
  rw [fieldValue_root]
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos hb]
    linarith

end InvariantIsing

end

end OAI
