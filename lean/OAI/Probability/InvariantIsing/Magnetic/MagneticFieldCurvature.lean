import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldMinimum
import OAI.Probability.InvariantIsing.Fields.FieldScalarLogCoshSecond

namespace OAI

/-! Strict bias convexity follows from the positive terminal curvature
and the nonnegative conditional variance terms in the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_pos (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ z, |a z| ≤ B) (hap : ∀ z, 0 < a z) (z : ℝ) :
    0 < fieldSpinTransition ζ v F a z := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hG ζ
  let μ := (gaussianReal z v).tilted (fun u => ζ * F u)
  have : IsProbabilityMeasure μ := MeasureTheory.isProbabilityMeasure_tilted hw
  have hi : Integrable a μ := (integrable_const B).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  have hs : Function.support a = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hap u).ne'
  change 0 < ∫ u, a u ∂μ
  apply (integral_pos_iff_support_of_nonneg (fun u => (hap u).le) hi).mpr
  rw [hs, measure_univ]
  exact (zero_lt_one : (0 : ENNReal) < 1)

lemma fieldScalarLogCoshSecond_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    0 < fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
      (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos z))
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hs := fieldScalarLogCoshSecond_regular L ht
    have hp := fieldSpinTransition_pos av.1 av.2 hv.1 hv.2 hs.1 hs.2 (ih ht) z
    have hm : Measurable Real.tanh := by
      change Measurable (fun z : ℝ => Real.tanh z)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hc := fieldSpinTransition_square_le av.1 av.2 hv.1 hv.2 ha.1 ha.2 z
    have hζ := (hL av List.mem_cons_self).le
    change 0 < fieldSpinTransition av.1 av.2 _ _ z + av.1 *
      (fieldSpinTransition av.1 av.2 _ _ z - (fieldScalarMean (av :: L) _ _ z) ^ 2)
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg hζ (sub_nonneg.mpr hc))

/-- Actual second bias derivative, with the root exponent fixed at zero. -/
def fieldBiasCurvature (h : FieldStep) : ℝ → ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarSecond (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (fun z => 1 / (Real.cosh z) ^ 2))

lemma fieldBiasCurvature_pos (h : FieldStep) (b : ℝ) : 0 < fieldBiasCurvature h b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hs := fieldScalarLogCoshSecond_regular (scalarFieldIncrements h) hL
  exact fieldSpinTransition_pos 0 _ hv.1 hv.2 hs.1 hs.2
    (fieldScalarLogCoshSecond_pos (scalarFieldIncrements h) hL) b

lemma hasDerivAt_fieldBiasMean (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldBiasMean h) (fieldBiasCurvature h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have ha := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  have hs := fieldScalarLogCoshSecond_regular (scalarFieldIncrements h) hL
  have hd := hasDerivAt_fieldSpinTransition 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 ha.1 ha.1 hs.1
    zero_le_one zero_le_one ha.2 ha.2 hs.2
    (hasDerivAt_fieldScalarLogCosh (scalarFieldIncrements h) hL)
    (hasDerivAt_fieldScalarLogCoshMean (scalarFieldIncrements h) hL) b
  simpa only [zero_mul, add_zero, fieldBiasMean, fieldBiasCurvature] using hd

lemma strictMono_fieldBiasMean (h : FieldStep) : StrictMono (fieldBiasMean h) := by
  apply strictMono_of_deriv_pos
  intro b
  rw [(hasDerivAt_fieldBiasMean h b).deriv]
  exact fieldBiasCurvature_pos h b

lemma strictConvexOn_fieldValue_bias (h : FieldStep) :
    StrictConvexOn ℝ Set.univ (fieldValue h) := by
  have he : deriv (fieldValue h) = fieldBiasMean h := by
    funext b
    exact (hasDerivAt_fieldValue_bias h b).deriv
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_fieldValue_bias h)
  rw [he]
  exact strictMono_fieldBiasMean h

lemma magneticBias_minimum_unique (h : FieldStep) {s b c : ℝ}
    (hb : ∀ x, magneticBiasObjective h s b ≤ magneticBiasObjective h s x)
    (hc : ∀ x, magneticBiasObjective h s c ≤ magneticBiasObjective h s x) : b = c := by
  apply (strictMono_fieldBiasMean h).injective
  rw [magneticBiasMean_eq_of_minimum h hb, magneticBiasMean_eq_of_minimum h hc]

end InvariantIsing

end

end OAI
