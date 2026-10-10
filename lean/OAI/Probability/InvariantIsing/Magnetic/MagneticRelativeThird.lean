import OAI.Probability.InvariantIsing.Magnetic.MagneticCenteredMoments

namespace OAI

/-! Relative third-derivative control through a physical tilted Gaussian
step. Unlike a uniform derivative bound, this remains useful at spin endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldThirdTransform_centered (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) (z : ℝ) :
    fieldThirdTransform ζ v F M Q R z =
      fieldSpinTransition ζ v F R z +
      3 * ζ * (fieldSpinTransition ζ v F (fun x => Q x * M x) z -
        fieldSpinTransition ζ v F Q z * fieldSpinTransition ζ v F M z) +
      ζ ^ 2 * fieldSpinTransition ζ v F
        (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 3) z := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  have hQM : fieldSpinTransition ζ v F (fun x => 2 * M x * Q x) z =
      2 * fieldSpinTransition ζ v F (fun x => Q x * M x) z := by
    change (∫ x, 2 * M x * Q x ∂μ) = 2 * ∫ x, Q x * M x ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hM3 : fieldSpinTransition ζ v F (fun x => (M x) ^ 2 * M x) z =
      fieldSpinTransition ζ v F (fun x => (M x) ^ 3) z := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hc := magnetic_centered_third μ hM bM
  change fieldSpinTransition ζ v F (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 3) z =
    fieldSpinTransition ζ v F (fun x => (M x) ^ 3) z -
      3 * fieldSpinTransition ζ v F M z * fieldSpinTransition ζ v F (fun x => (M x) ^ 2) z +
      2 * (fieldSpinTransition ζ v F M z) ^ 3 at hc
  rw [hc]
  unfold fieldThirdTransform fieldCurvatureTransform
  rw [hQM, hM3]
  ring

theorem fieldThirdTransform_relative_bound {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (bM : ∀ x, |M x| ≤ 1) {B C : ℝ} (bQ : ∀ x, |Q x| ≤ B)
    (hQpos : ∀ x, 0 ≤ Q x) (hC : 0 ≤ C)
    (bR : ∀ x, |R x| ≤ C * Q x) (z : ℝ) :
    |fieldThirdTransform ζ v F M Q R z| ≤
      (C + 8 * ζ) * fieldCurvatureTransform ζ v F M Q z := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  let q := ∫ x, Q x ∂μ
  let V := ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ
  have hq : 0 ≤ q := integral_nonneg hQpos
  have hV : 0 ≤ V := integral_nonneg fun _ => sq_nonneg _
  have hiQ : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bQ x)
  have hiR : Integrable R μ := (hiQ.const_mul C).mono' hR.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bR x)
  have hRb : |∫ x, R x ∂μ| ≤ C * q := by
    calc
      _ ≤ ∫ x, |R x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * Q x ∂μ := integral_mono hiR.abs (hiQ.const_mul C) bR
      _ = _ := integral_const_mul _ _
  have hCov := magnetic_weighted_centered_bound μ hM hQ bM bQ hQpos
  have hThird := magnetic_centered_third_bound μ hM bM
  have hcurv : fieldCurvatureTransform ζ v F M Q z = q + ζ * V := by
    dsimp only [q, V]
    rw [magnetic_centered_second μ hM bM]
    rfl
  rw [fieldThirdTransform_centered ζ v hF hG hM bM, hcurv]
  change |(∫ x, R x ∂μ) + 3 * ζ * ((∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)) +
    ζ ^ 2 * (∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ)| ≤ (C + 8 * ζ) * (q + ζ * V)
  calc
    _ ≤ |∫ x, R x ∂μ| + 3 * ζ * |(∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)| +
        ζ ^ 2 * |∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ| := by
      have ha := abs_add_le ((∫ x, R x ∂μ) + 3 * ζ *
        ((∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)))
        (ζ ^ 2 * (∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ))
      have hb := abs_add_le (∫ x, R x ∂μ)
        (3 * ζ * ((∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)))
      rw [abs_mul, abs_of_nonneg (sq_nonneg ζ)] at ha
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * ζ)] at hb
      linarith
    _ ≤ C * q + 3 * ζ * (2 * q) + ζ ^ 2 * (2 * V) := by
      exact add_le_add (add_le_add hRb (mul_le_mul_of_nonneg_left hCov (by positivity)))
        (mul_le_mul_of_nonneg_left hThird (sq_nonneg ζ))
    _ ≤ (C + 8 * ζ) * (q + ζ * V) := by
      have h1 := mul_nonneg hζ hq
      have h2 := mul_nonneg (mul_nonneg hC hζ) hV
      have h3 := mul_nonneg (sq_nonneg ζ) hV
      nlinarith

def magneticThirdRatioCap : List (ℝ × ℝ≥0) → ℝ
  | [] => 2
  | av :: L => magneticThirdRatioCap L + 8 * |av.1|

lemma magneticThirdRatioCap_nonneg (L : List (ℝ × ℝ≥0)) :
    0 ≤ magneticThirdRatioCap L := by
  induction L with
  | nil => norm_num [magneticThirdRatioCap]
  | cons av L ih => exact add_nonneg ih (mul_nonneg (by norm_num) (abs_nonneg _))

lemma field_logCosh_third_relative (z : ℝ) :
    |-2 * Real.tanh z / (Real.cosh z) ^ 2| ≤ 2 * (1 / (Real.cosh z) ^ 2) := by
  have hp : 0 < (Real.cosh z) ^ 2 := sq_pos_of_pos (Real.cosh_pos z)
  calc
    _ = 2 * |Real.tanh z| * (1 / (Real.cosh z) ^ 2) := by
      rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hp]
      ring
    _ ≤ 2 * 1 * (1 / (Real.cosh z) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (field_abs_tanh_le_one z) (by norm_num))
        (one_div_nonneg.mpr hp.le)
    _ = _ := by ring

theorem fieldScalarLogCoshThird_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    |fieldScalarThird L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2)
        (fun x => -2 * Real.tanh x / (Real.cosh x) ^ 2) z| ≤
      magneticThirdRatioCap L * fieldScalarSecond L
        (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact field_logCosh_third_relative z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hr := fieldScalarThird_regular L ht measurable_logCosh logCosh_linearGrowth
      hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
      field_tanh_second_bound field_logCosh_third_bound
    have hp := (hL av List.mem_cons_self).le
    have he := fieldThirdTransform_relative_bound hp av.2 hv.1 hv.2 ha.1 hq.1 hr.1
      ha.2 hq.2 (fun x => (fieldScalarLogCoshSecond_pos L ht x).le)
      (magneticThirdRatioCap_nonneg L) (ih ht) z
    simpa only [fieldScalarThird, fieldScalarSecond, fieldScalarMean, magneticThirdRatioCap,
      abs_of_nonneg hp, fieldCurvatureTransform] using he

lemma fieldBiasThird_relative (h : FieldStep) (b : ℝ) :
    |fieldBiasThird h b| ≤ magneticThirdRatioCap (scalarFieldIncrements h) *
      fieldBiasCurvature h b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular _ hL measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have ha := fieldScalarMean_regular _ hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hq := fieldScalarLogCoshSecond_regular _ hL
  have hr := fieldScalarThird_regular _ hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound
  have he := fieldThirdTransform_relative_bound (by norm_num : (0 : ℝ) ≤ 0)
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 ha.1 hq.1 hr.1 ha.2 hq.2
    (fun x => (fieldScalarLogCoshSecond_pos _ hL x).le)
    (magneticThirdRatioCap_nonneg _) (fieldScalarLogCoshThird_relative _ hL) b
  simpa only [fieldThirdTransform, zero_mul, mul_zero, add_zero, fieldCurvatureTransform,
    fieldBiasThird, fieldBiasCurvature] using he

lemma magneticCurvatureSlope_bound (h : FieldStep) (s : ℝ) :
    |magneticCurvatureSlope h s| ≤ magneticThirdRatioCap (scalarFieldIncrements h) := by
  unfold magneticCurvatureSlope
  rw [abs_div, abs_of_pos (magneticCurvature_pos h s)]
  apply (div_le_iff₀ (magneticCurvature_pos h s)).mpr
  exact fieldBiasThird_relative h (magneticBias h s)

end InvariantIsing

end

end OAI
