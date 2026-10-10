import OAI.Combinatorics.SparsestCut.PositiveKernels

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.KernelApprox

def profile (t : ℝ) : ℝ := 1 - Real.exp (-1/(2*t^2))

lemma profile_nonneg (t : ℝ) : 0 ≤ profile t := by
  unfold profile
  have h : -1/(2*t^2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  linarith [Real.exp_le_one_iff.mpr h]

lemma profile_le_one (t : ℝ) : profile t ≤ 1 := by
  unfold profile
  linarith [Real.exp_pos (-1/(2*t^2))]

lemma profile_le_inv_sq (t : ℝ) : profile t ≤ 1/(2*t^2) := by
  have h := Real.add_one_le_exp (-1/(2*t^2))
  unfold profile
  rw [neg_div] at h ⊢
  linarith

lemma profile_pos {t : ℝ} (ht : t ≠ 0) : 0 < profile t := by
  unfold profile
  have h : -1/(2*t^2) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  linarith [Real.exp_lt_one_iff.mpr h]

lemma profile_measurable : Measurable profile := by unfold profile; fun_prop

lemma profile_integrable_lower : IntegrableOn profile (Ioc 0 1) := by
  apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) 1) (by simp)).mono'
    profile_measurable.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t)] using profile_le_one t

lemma profile_integrable_upper : IntegrableOn profile (Ioi 1) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (1/2 : ℝ)
  apply hi.mono' profile_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 1 < t at ht
  have he : (1/2 : ℝ)*t^(-2 : ℝ) = 1/(2*t^2) := by
    rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t), he] using profile_le_inv_sq t

lemma profile_integrable : IntegrableOn profile (Ioi 0) := by
  have h := profile_integrable_lower.union profile_integrable_upper
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using h

noncomputable def cstar : ℝ := 2 * ∫ t in Ioi (0 : ℝ), profile t

lemma cstar_pos : 0 < cstar := by
  have hp : 0 < ∫ t in Ioi (0 : ℝ), profile t := by
    apply (integral_pos_iff_support_of_nonneg_ae _ profile_integrable).mpr
    · have hs : Ioi (0 : ℝ) ⊆ Function.support profile := by
        intro t ht
        exact ne_of_gt (profile_pos (ne_of_gt ht))
      have hc : (volume.restrict (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) ≠ 0 := by simp
      exact bot_lt_iff_ne_bot.mpr (ne_bot_of_le_ne_bot hc (measure_mono hs))
    · filter_upwards with t using profile_nonneg t
  exact mul_pos (by norm_num) hp

def scaled (r t : ℝ) : ℝ := 1-Real.exp (-r^2/(2*t^2))

lemma scaled_eq_profile (r t : ℝ) : scaled r t = profile (t/r) := by
  by_cases hr : r = 0
  · simp [hr, scaled, profile]
  by_cases ht : t = 0
  · simp [ht, scaled, profile]
  unfold scaled profile
  congr 2
  field_simp

lemma scaled_nonneg (r t : ℝ) : 0 ≤ scaled r t := by
  rw [scaled_eq_profile]; exact profile_nonneg _

lemma scaled_le_one (r t : ℝ) : scaled r t ≤ 1 := by
  rw [scaled_eq_profile]; exact profile_le_one _

lemma scaled_le_tail (r t : ℝ) : scaled r t ≤ r^2/(2*t^2) := by
  have h := Real.add_one_le_exp (-r^2/(2*t^2))
  unfold scaled
  rw [neg_div] at h ⊢
  linarith

lemma scaled_measurable (r : ℝ) : Measurable (scaled r) := by unfold scaled; fun_prop

lemma scaled_integrable_lower (r : ℝ) {a : ℝ} (_ha : 0 ≤ a) :
    IntegrableOn (scaled r) (Ioc 0 a) := by
  apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) a) (by simp)).mono'
    (scaled_measurable r).aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg r t)] using scaled_le_one r t

lemma scaled_integrable_upper (r : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (scaled r) (Ioi a) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul (r^2/2)
  apply hi.mono' (scaled_measurable r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change a < t at ht
  have he : (r^2/2)*t^(-2 : ℝ) = r^2/(2*t^2) := by
    rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg r t), he] using scaled_le_tail r t

lemma scaled_integrable (r : ℝ) : IntegrableOn (scaled r) (Ioi 0) := by
  have h := (scaled_integrable_lower r (by norm_num : (0 : ℝ) ≤ 1)).union
    (scaled_integrable_upper r (by norm_num : (0 : ℝ) < 1))
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using h

lemma full_integral {r : ℝ} (hr : 0 ≤ r) :
    2 * (∫ t in Ioi (0 : ℝ), scaled r t) = cstar*r := by
  rcases eq_or_lt_of_le hr with hz | hr
  · simp [← hz, scaled]
  simp_rw [scaled_eq_profile, div_eq_inv_mul]
  rw [integral_comp_mul_left_Ioi profile 0 (inv_pos.mpr hr)]
  simp only [mul_zero, inv_inv, smul_eq_mul, cstar]
  ring

lemma lower_tail_bound (r : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Ioc (0 : ℝ) a, scaled r t) ≤ a := by
  have h := integral_mono (scaled_integrable_lower r ha)
    (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) a) (by simp))
    (fun t => scaled_le_one r t)
  simpa [integral_const, Real.volume_real_Ioc, ha] using h

lemma upper_tail_bound (r : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi b, scaled r t) ≤ r^2/(2*b) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hb).const_mul (r^2/2)
  calc
    _ ≤ ∫ t in Ioi b, (r^2/2)*t^(-2 : ℝ) := by
      apply integral_mono_ae (scaled_integrable_upper r hb) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change b < t at ht
      rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
      exact (scaled_le_tail r t).trans_eq (by ring)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hb]
      norm_num
      rw [Real.rpow_neg_one]
      ring

lemma truncated_error {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (hab : a ≤ b) :
    |2 * (∫ t in Ioc a b, scaled r t) - cstar*r| ≤ 2*a + r^2/b := by
  have hb : 0 < b := ha.trans_le hab
  have hi1 := scaled_integrable_lower r ha.le
  have hi2 : IntegrableOn (scaled r) (Ioc a b) :=
    (scaled_integrable r).mono_set (fun t ht => ha.trans ht.1)
  have hi3 := scaled_integrable_upper r hb
  have he : (∫ t in Ioi (0 : ℝ), scaled r t) =
      (∫ t in Ioc (0 : ℝ) a, scaled r t) + (∫ t in Ioc a b, scaled r t) +
      ∫ t in Ioi b, scaled r t := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le, setIntegral_union]
    · rw [← Ioc_union_Ioc_eq_Ioc ha.le hab, setIntegral_union]
      · exact Ioc_disjoint_Ioc_of_le le_rfl
      · exact measurableSet_Ioc
      · exact hi1
      · exact hi2
    · exact Ioc_disjoint_Ioi_same
    · exact measurableSet_Ioi
    · exact scaled_integrable_lower r hb.le
    · exact hi3
  have hx := full_integral hr
  rw [he] at hx
  have hn1 : 0 ≤ ∫ t in Ioc (0 : ℝ) a, scaled r t := integral_nonneg (fun _ => scaled_nonneg _ _)
  have hn3 : 0 ≤ ∫ t in Ioi b, scaled r t := integral_nonneg (fun _ => scaled_nonneg _ _)
  have hu1 := lower_tail_bound r ha.le
  have hu3 := upper_tail_bound r hb
  have he' : r^2/b = 2*(r^2/(2*b)) := by ring
  rw [abs_of_nonpos (by linarith), he']
  linarith

end UniformSparsestCut.KernelApprox

end

end OAI
