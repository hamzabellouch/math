import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarContinuation
import OAI.Probability.InvariantIsing.Magnetic.MagneticBiasEndpoint

namespace OAI

/-! Endpoint decay for the literal finite-field conditional square levels.
The inverse-coordinate weighted curvature has zero boundary values, proved
from bounded ordinary derivatives rather than an asymptotic expansion. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma fieldBiasMean_tendsto_one (h : FieldStep) :
    Tendsto (fieldBiasMean h) atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    let s := (max l (-1) + 1) / 2
    have hm : max l (-1 : ℝ) < 1 := max_lt hl (by norm_num)
    have hs : |s| < 1 := by
      apply abs_lt.mpr
      dsimp only [s]
      constructor <;> linarith [le_max_right l (-1 : ℝ)]
    have hls : l < s := by dsimp only [s]; linarith [le_max_left l (-1 : ℝ)]
    filter_upwards [eventually_gt_atTop (magneticBias h s)] with b hb
    have hh := strictMono_fieldBiasMean h hb
    rw [fieldBiasMean_magneticBias h hs] at hh
    exact hls.trans hh
  · intro u hu
    exact Eventually.of_forall fun b => (fieldBiasMean_strict_bounds h b).2.trans hu

lemma fieldBiasMean_tendsto_neg_one (h : FieldStep) :
    Tendsto (fieldBiasMean h) atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall fun b => hl.trans (fieldBiasMean_strict_bounds h b).1
  · intro u hu
    let s := (min u 1 - 1) / 2
    have hm : (-1 : ℝ) < min u 1 := lt_min hu (by norm_num)
    have hs : |s| < 1 := by
      apply abs_lt.mpr
      dsimp only [s]
      constructor <;> linarith [min_le_right u (1 : ℝ)]
    have hsu : s < u := by dsimp only [s]; linarith [min_le_left u (1 : ℝ)]
    filter_upwards [eventually_lt_atBot (magneticBias h s)] with b hb
    have hh := strictMono_fieldBiasMean h hb
    rw [fieldBiasMean_magneticBias h hs] at hh
    exact hh.trans hsu

lemma magneticLevelAtBias_tendsto_one (h : FieldStep) (i : Fin (h.depth + 1)) :
    Tendsto (fun b => magneticLevelAtBias h b i) atTop (𝓝 (1 : ℝ)) := by
  have hs := (fieldBiasMean_tendsto_one h).pow 2
  norm_num only [one_pow] at hs
  exact hs.squeeze tendsto_const_nhds (fun b => fieldBiasMean_sq_le_magneticLevel h b i)
    (fun b => (magneticLevelAtBias_mem_unit h b i).2)

lemma magneticLevelAtBias_tendsto_neg_one (h : FieldStep) (i : Fin (h.depth + 1)) :
    Tendsto (fun b => magneticLevelAtBias h b i) atBot (𝓝 (1 : ℝ)) := by
  have hs := (fieldBiasMean_tendsto_neg_one h).pow 2
  norm_num only [neg_sq, one_pow] at hs
  exact hs.squeeze tendsto_const_nhds (fun b => fieldBiasMean_sq_le_magneticLevel h b i)
    (fun b => (magneticLevelAtBias_mem_unit h b i).2)

lemma magnetic_derivative_tendsto_zero_atBot {F G D : ℝ → ℝ} {c L : ℝ}
    (hL : 0 ≤ L) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : ∀ x, HasDerivAt G (D x) x) (hD : ∀ x, |D x| ≤ L)
    (hlimit : Tendsto F atBot (𝓝 c)) : Tendsto G atBot (𝓝 0) := by
  have hdF (x : ℝ) : HasDerivAt (fun y => F (-y)) (-G (-x)) x := by
    convert (hF (-x)).comp x (hasDerivAt_neg x) using 1 <;> first | rfl | simp
  have hdG (x : ℝ) : HasDerivAt (fun y => -G (-y)) (D (-x)) x := by
    convert ((hG (-x)).comp x (hasDerivAt_neg x)).neg using 1 <;> first | rfl | simp
  have hh := magnetic_derivative_tendsto_zero hL hdF hdG (fun x => hD (-x))
    (hlimit.comp tendsto_neg_atTop_atBot)
  simpa only [Function.comp_def, neg_neg, neg_zero] using hh.neg.comp tendsto_neg_atBot_atTop

lemma MagneticContinuationJet.first_tendsto_zero (J : MagneticContinuationJet)
    {c : ℝ} (hJ : Tendsto J.value atTop (𝓝 c)) : Tendsto J.first atTop (𝓝 0) := by
  obtain ⟨L, hL, bL⟩ := J.bSecond
  exact magnetic_derivative_tendsto_zero hL J.dValue J.dFirst bL hJ

lemma MagneticContinuationJet.second_tendsto_zero (J : MagneticContinuationJet)
    {c : ℝ} (hJ : Tendsto J.value atTop (𝓝 c)) : Tendsto J.second atTop (𝓝 0) := by
  obtain ⟨L, hL, bL⟩ := J.bThird
  exact magnetic_derivative_tendsto_zero hL J.dFirst J.dSecond bL (J.first_tendsto_zero hJ)

lemma MagneticContinuationJet.first_tendsto_zero_atBot (J : MagneticContinuationJet)
    {c : ℝ} (hJ : Tendsto J.value atBot (𝓝 c)) : Tendsto J.first atBot (𝓝 0) := by
  obtain ⟨L, hL, bL⟩ := J.bSecond
  exact magnetic_derivative_tendsto_zero_atBot hL J.dValue J.dFirst bL hJ

lemma MagneticContinuationJet.second_tendsto_zero_atBot (J : MagneticContinuationJet)
    {c : ℝ} (hJ : Tendsto J.value atBot (𝓝 c)) : Tendsto J.second atBot (𝓝 0) := by
  obtain ⟨L, hL, bL⟩ := J.bThird
  exact magnetic_derivative_tendsto_zero_atBot hL J.dFirst J.dSecond bL
    (J.first_tendsto_zero_atBot hJ)

lemma magneticContinuation_weighted_endpoint (h : FieldStep) (i : Fin (h.depth + 1))
    (J : MagneticContinuationJet) (hJ : J.value = fun b => magneticLevelAtBias h b i) :
    Tendsto (fun s => J.second (magneticBias h s) - J.first (magneticBias h s) *
        (fieldBiasThird h (magneticBias h s) / fieldBiasCurvature h (magneticBias h s)))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  obtain ⟨L, hL, bL⟩ := J.bSecond
  obtain ⟨K, hK, bK⟩ := J.bThird
  have hv : Tendsto J.value atTop (𝓝 (1 : ℝ)) := by
    rw [hJ]
    exact magneticLevelAtBias_tendsto_one h i
  exact (magnetic_weighted_continuation_limit h hL hK J.dValue J.dFirst J.dSecond bL bK hv).comp
    (magneticBias_tendsto_one h)

lemma magneticContinuation_weighted_neg_endpoint (h : FieldStep) (i : Fin (h.depth + 1))
    (J : MagneticContinuationJet) (hJ : J.value = fun b => magneticLevelAtBias h b i) :
    Tendsto (fun s => J.second (magneticBias h s) - J.first (magneticBias h s) *
        (fieldBiasThird h (magneticBias h s) / fieldBiasCurvature h (magneticBias h s)))
      (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  have hv : Tendsto J.value atBot (𝓝 (1 : ℝ)) := by
    rw [hJ]
    exact magneticLevelAtBias_tendsto_neg_one h i
  have hg := J.first_tendsto_zero_atBot hv
  have hd := J.second_tendsto_zero_atBot hv
  have hp : Tendsto (fun b => J.first b * (fieldBiasThird h b / fieldBiasCurvature h b))
      atBot (𝓝 0) := by
    apply squeeze_zero_norm (fun b => ?_)
      (show Tendsto (fun b => |J.first b| * magneticThirdRatioCap (scalarFieldIncrements h))
          atBot (𝓝 0) by
        simpa only [Real.norm_eq_abs, abs_zero, zero_mul] using
          hg.norm.mul_const (magneticThirdRatioCap (scalarFieldIncrements h)))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (fieldBiasThird_quotient_bound h b) (abs_nonneg _)
  have hh := hd.sub hp
  simp only [sub_zero] at hh
  exact hh.comp (magneticBias_tendsto_neg_one h)

end InvariantIsing

end

end OAI
