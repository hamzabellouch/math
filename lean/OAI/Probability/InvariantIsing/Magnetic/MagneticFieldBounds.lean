import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldCurvature
import OAI.Probability.InvariantIsing.Fields.FieldFiniteDomain

namespace OAI

/-! The exact canonical bias bounds (mag:bias-bounds) on every finite
field partition, including tied heights and a degenerate root increment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma convexOn_logcosh : ConvexOn ℝ Set.univ (fun b : ℝ => Real.log (Real.cosh b)) := by
  have hc : Continuous (fun b : ℝ => Real.log (Real.cosh b)) :=
    continuous_iff_continuousAt.mpr fun b =>
      ((Real.hasDerivAt_cosh b).log (Real.cosh_pos b).ne').continuousAt
  have hd : deriv (fun b : ℝ => Real.log (Real.cosh b)) = Real.tanh := by
    funext b
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      ((Real.hasDerivAt_cosh b).log (Real.cosh_pos b).ne').deriv
  have hm : StrictMono Real.tanh := strictMono_of_hasDerivAt_pos field_hasDerivAt_tanh
    (fun b => one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos b)))
  apply (StrictMono.strictConvexOn_univ_of_deriv hc ?_).convexOn
  rw [hd]
  exact hm

lemma logcosh_le_gaussianOperator {F : ℝ → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {a : ℝ} (ha : 0 ≤ a) (v : ℝ≥0)
    (hl : ∀ z, Real.log (Real.cosh z) ≤ F z) (z : ℝ) :
    Real.log (Real.cosh z) ≤ gaussianOperator a v F z := by
  have hi : Integrable (fun u : ℝ => u) (gaussianReal z v) := IsGaussian.integrable_id
  have hlog := field_gaussian_linear_integrable v z measurable_logCosh logCosh_linearGrowth
  have hc : Continuous (fun b : ℝ => Real.log (Real.cosh b)) :=
    continuous_iff_continuousAt.mpr fun b =>
      ((Real.hasDerivAt_cosh b).log (Real.cosh_pos b).ne').continuousAt
  have hj := convexOn_logcosh.map_integral_le hc.continuousOn isClosed_univ
    (ae_of_all (gaussianReal z v) (fun u => mem_univ u)) hi hlog
  rw [integral_id_gaussianReal] at hj
  have hf := field_gaussian_linear_integrable v z hF hG
  have hmean := hj.trans (integral_mono hlog hf hl)
  by_cases ha0 : a = 0
  · subst a
    rwa [gaussianOperator_eq_gaussian_integral v hF]
  · rw [gaussianOperator_eq_gaussian_exp_integral ha0 v hF]
    exact hmean.trans (mean_le_log_moment_div (gaussianReal z v) hf
      (lt_of_le_of_ne ha (Ne.symm ha0))
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG a))

lemma logcosh_le_fieldScalarValue (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    Real.log (Real.cosh z) ≤
      fieldScalarValue L (fun b => Real.log (Real.cosh b)) z := by
  induction L generalizing z with
  | nil => exact le_rfl
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    exact logcosh_le_gaussianOperator hv.1 hv.2 (hL av List.mem_cons_self).le av.2 (ih ht) z

lemma fieldValue_ge_logcosh_sub_height (h : FieldStep) (b : ℝ) :
    Real.log (Real.cosh b) - h.height (Fin.last h.depth) / 2 ≤ fieldValue h b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hl := logcosh_le_gaussianOperator hv.1 hv.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0))
    (logcosh_le_fieldScalarValue (scalarFieldIncrements h) hL) b
  change Real.log (Real.cosh b) ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hl
  rw [fieldValue_root]
  exact sub_le_sub_right hl _

lemma fieldValue_le_logcosh (h : FieldStep) (b : ℝ) :
    fieldValue h b ≤ Real.log (Real.cosh b) := by
  have hv := fieldValue_majorant_sum h (show (0:ℝ) < 1 by norm_num) le_rfl b
  rw [fieldMajorant_eq_logcosh (show (1:ℝ) ≠ 0 by norm_num),
    List.map_ofFn, List.sum_ofFn] at hv
  simp only [Function.comp_def, one_mul, div_one, inv_one, sub_self, zero_mul, add_zero] at hv
  have hs : (∑ i : Fin (h.depth + 1), max (fieldIncrement h i).1 1 *
      (fieldIncrement h i).2 / 2) = h.height (Fin.last h.depth) / 2 := by
    have hmax (i : Fin (h.depth + 1)) : max (fieldIncrement h i).1 1 = 1 := by
      apply max_eq_right
      change h.cut i.castSucc ≤ 1
      rw [← h.last]
      exact h.ordered_cut.monotone (Fin.le_last _)
    simp_rw [hmax, one_mul]
    rw [← Finset.sum_div, fieldIncrement_sum]
  rw [hs] at hv
  linarith

lemma fieldValue_canonical_bias_bounds (h : FieldStep) (b : ℝ) :
    Real.log (Real.cosh b) ≤ fieldValue h b + h.height (Fin.last h.depth) / 2 ∧
      fieldValue h b + h.height (Fin.last h.depth) / 2 ≤
        Real.log (Real.cosh b) + h.height (Fin.last h.depth) / 2 := by
  constructor
  · linarith [fieldValue_ge_logcosh_sub_height h b]
  · linarith [fieldValue_le_logcosh h b]

end InvariantIsing

end

end OAI
