import OAI.Analysis.LpDimension.Sampling

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u

namespace SubpolynomialLp

def fourierCutoff (x : ℝ) : ℝ := ∫ t in Set.Ioc (0:ℝ) 1, 1-Real.cos (t*x)

lemma fourierCutoff_nonneg (x : ℝ) : 0 ≤ fourierCutoff x :=
  integral_nonneg (fun _t => sub_nonneg.mpr (Real.cos_le_one _))

lemma fourierCutoff_le_two (x : ℝ) : fourierCutoff x ≤ 2 := by
  calc
    fourierCutoff x ≤ ∫ _ in Set.Ioc (0:ℝ) 1, (2:ℝ) := by
      apply integral_mono
      · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
      · exact integrable_const _
      · intro t
        have := Real.neg_one_le_cos (t*x)
        linarith
    _ = 2 := by simp

lemma fourierCutoff_eq (x : ℝ) (hx : x ≠ 0) :
    fourierCutoff x = 1-Real.sin x/x := by
  rw [fourierCutoff, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_sub intervalIntegrable_const ((by fun_prop : Continuous (fun t : ℝ => Real.cos (t*x))).intervalIntegrable 0 1),
    intervalIntegral.integral_const, intervalIntegral.integral_comp_mul_right _ hx,
    integral_cos]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma fourierCutoff_ge_half (x : ℝ) (hx : 2 ≤ |x|) : 1/2 ≤ fourierCutoff x := by
  have hxn : x ≠ 0 := by intro h; norm_num [h] at hx
  have ha : 0 < |x| := by linarith
  rw [fourierCutoff_eq x hxn]
  have h : Real.sin x/x ≤ 1/2 := by
    calc
      Real.sin x/x ≤ |Real.sin x/x| := le_abs_self _
      _ = |Real.sin x|/|x| := abs_div _ _
      _ ≤ 1/|x| := div_le_div_of_nonneg_right (Real.abs_sin_le_one x) ha.le
      _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hx
  linarith

@[fun_prop] lemma fourierCutoff_continuous : Continuous fourierCutoff := by
  apply continuous_of_dominated
    (bound := fun _ : ℝ => (2:ℝ))
  · intro x
    fun_prop
  · intro x
    exact ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      have := Real.neg_one_le_cos (t*x)
      linarith)
  · exact integrable_const _
  · exact ae_of_all _ (fun t => by fun_prop)

lemma real_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun μ t).re = ∫ x, Real.cos (t*x) ∂μ := by
  rw [charFun_apply_real]
  change RCLike.re (∫ x, Complex.exp ((t:ℂ)*x*Complex.I) ∂μ) = _
  rw [← integral_re]
  · apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp [Complex.exp_re])
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

lemma fourierCutoff_average (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    (∫ x, fourierCutoff (b*x) ∂μ) =
      ∫ t in Set.Ioc (0:ℝ) 1, 1-(charFun μ (t*b)).re := by
  have hi : Integrable (Function.uncurry (fun x t : ℝ => 1-Real.cos (t*(b*x))))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine (integrable_const (2:ℝ)).mono' (by fun_prop) (ae_of_all _ (fun z => ?_))
    change |1-Real.cos (z.2*(b*z.1))| ≤ 2
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    have := Real.neg_one_le_cos (z.2*(b*z.1))
    change 1-Real.cos (z.2*(b*z.1)) ≤ 2
    linarith
  change (∫ x, (∫ t in Set.Ioc (0:ℝ) 1, 1-Real.cos (t*(b*x))) ∂μ) = _
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    dsimp only
    rw [integral_sub (integrable_const _) ((integrable_const (1:ℝ)).mono'
      (by fun_prop) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*(b*x)))))]
    simp only [integral_const, probReal_univ, one_smul, real_charFun, mul_assoc])

lemma stable_tail_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ)
    (hp : 0 < p) (hc : 0 ≤ c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p))
    (a : ℝ) (ha : 0 < a) :
    μ.real {x : ℝ | a < |x|} ≤ (2*c*2^p)*a^(-p) := by
  have hi : Integrable (fun x => fourierCutoff ((2/a)*x)) μ := by
    refine (integrable_const (2:ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fourierCutoff_nonneg _)]
      exact fourierCutoff_le_two _)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => fourierCutoff_nonneg ((2/a)*x))) hi (1/2)
  have hs : μ.real {x : ℝ | a < |x|} ≤ μ.real {x : ℝ | 1/2 ≤ fourierCutoff ((2/a)*x)} := by
    apply measureReal_mono ?_ (by finiteness)
    intro x hx
    apply fourierCutoff_ge_half
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) ha)]
    have h : a ≤ |x| := le_of_lt hx
    calc
      2 = (2/a)*a := by field_simp
      _ ≤ (2/a)*|x| := mul_le_mul_of_nonneg_left h (by positivity)
  have hb : (∫ x, fourierCutoff ((2/a)*x) ∂μ) ≤ c*(2/a)^p := by
    rw [fourierCutoff_average]
    calc
      (∫ t in Set.Ioc (0:ℝ) 1, 1-(charFun μ (t*(2/a))).re) ≤
          ∫ _ in Set.Ioc (0:ℝ) 1, c*(2/a)^p := by
        apply integral_mono_ae
        · apply Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
        · exact integrable_const _
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          rw [hcf]
          have he := Real.add_one_le_exp (-c*|t*(2/a)|^p)
          have ht' : |t*(2/a)| ≤ 2/a := by
            rw [abs_of_nonneg (mul_nonneg ht.1.le (by positivity))]
            exact mul_le_of_le_one_left (by positivity) ht.2
          have hpw := Real.rpow_le_rpow (abs_nonneg _) ht' hp.le
          nlinarith [mul_le_mul_of_nonneg_left hpw hc]
      _ = c*(2/a)^p := by simp
  have he : (2/a)^p = 2^p*a^(-p) := by
    rw [Real.div_rpow (by norm_num) ha.le, Real.rpow_neg ha.le]
    rfl
  rw [he] at hb
  nlinarith

lemma one_sub_cos_quadratic_lower (x : ℝ) (hx : |x| ≤ 2) :
    x^2/8 ≤ 1-Real.cos x := by
  have hpi : (1/2:ℝ) ≤ 2/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  have ha : |x/2| ≤ Real.pi/2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [Real.two_le_pi]
  have h := Real.mul_abs_le_abs_sin ha
  have habs : |x|/4 ≤ |Real.sin (x/2)| := by
    calc
      |x|/4 = (1/2)*|x/2| := by rw [abs_div]; norm_num; ring
      _ ≤ (2/Real.pi)*|x/2| := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
      _ ≤ _ := h
  have hs := sq_le_sq₀ (by positivity : (0:ℝ) ≤ |x|/4) (abs_nonneg (Real.sin (x/2))) |>.mpr habs
  rw [div_pow, sq_abs, sq_abs, Real.sin_sq_eq_half_sub] at hs
  have he : 2*(x/2) = x := by ring
  rw [he] at hs
  nlinarith

lemma fourierCutoff_quadratic (x : ℝ) : min (x^2) 1 ≤ 24*fourierCutoff x := by
  by_cases hx : 2 ≤ |x|
  · have := fourierCutoff_ge_half x hx
    have := min_le_right (x^2) 1
    linarith
  · have hx' : |x| ≤ 2 := le_of_lt (lt_of_not_ge hx)
    have h : x^2/24 ≤ fourierCutoff x := by
      calc
        x^2/24 = ∫ t in Set.Ioc (0:ℝ) 1, (t*x)^2/8 := by
          rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
          simp_rw [show ∀ t : ℝ, (t*x)^2/8 = (x^2/8)*t^2 by intro t; ring]
          rw [intervalIntegral.integral_const_mul, integral_pow]
          norm_num
          ring
        _ ≤ fourierCutoff x := by
          apply integral_mono_ae
          · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
          · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            apply one_sub_cos_quadratic_lower
            rw [abs_mul, abs_of_pos ht.1]
            exact (mul_le_of_le_one_left (abs_nonneg x) ht.2).trans hx'
    have := min_le_left (x^2) 1
    linarith

lemma stable_fourier_average_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c b : ℝ)
    (hp : 0 < p) (hc : 0 ≤ c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p)) :
    (∫ x, fourierCutoff (b*x) ∂μ) ≤ c*|b|^p := by
  rw [fourierCutoff_average]
  calc
    (∫ t in Set.Ioc (0:ℝ) 1, 1-(charFun μ (t*b)).re) ≤
        ∫ _ in Set.Ioc (0:ℝ) 1, c*|b|^p := by
      apply integral_mono_ae
      · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [hcf]
        have he := Real.add_one_le_exp (-c*|t*b|^p)
        have hb : |t*b| ≤ |b| := by
          rw [abs_mul, abs_of_pos ht.1]
          exact mul_le_of_le_one_left (abs_nonneg b) ht.2
        have hpw := Real.rpow_le_rpow (abs_nonneg _) hb hp.le
        nlinarith [mul_le_mul_of_nonneg_left hpw hc]
    _ = c*|b|^p := by simp

lemma stable_capped_second_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ)
    (hp : 0 < p) (hc : 0 ≤ c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p))
    (a : ℝ) (ha : 0 < a) :
    (∫ x, min (x^2) (a^2) ∂μ) ≤ 24*c*a^(2-p) := by
  have hi : Integrable (fun x => fourierCutoff (a⁻¹*x)) μ := by
    refine (integrable_const (2:ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fourierCutoff_nonneg _)]
      exact fourierCutoff_le_two _)
  have hj : Integrable (fun x : ℝ => min (x^2) (a^2)) μ := by
    refine (integrable_const (a^2)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact min_le_right _ _)
  have hpt (x : ℝ) : min (x^2) (a^2) = a^2*min ((a⁻¹*x)^2) 1 := by
    rw [mul_min_of_nonneg _ _ (sq_nonneg a), mul_one, mul_pow]
    congr 2
    field_simp
  calc
    (∫ x, min (x^2) (a^2) ∂μ) ≤ ∫ x, (24*a^2)*fourierCutoff (a⁻¹*x) ∂μ := by
      apply integral_mono hj (hi.const_mul _)
      intro x
      dsimp only
      rw [hpt]
      nlinarith [mul_le_mul_of_nonneg_left (fourierCutoff_quadratic (a⁻¹*x)) (sq_nonneg a)]
    _ = (24*a^2)*∫ x, fourierCutoff (a⁻¹*x) ∂μ := integral_const_mul _ _
    _ ≤ (24*a^2)*(c*|a⁻¹|^p) := mul_le_mul_of_nonneg_left
      (stable_fourier_average_upper μ p c a⁻¹ hp hc hcf) (by positivity)
    _ = 24*c*a^(2-p) := by
      rw [abs_of_pos (inv_pos.mpr ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
        show 24*a^2*(c*a^(-p)) = 24*c*(a^2*a^(-p)) by ring,
        ← Real.rpow_natCast a 2, ← Real.rpow_add ha]
      rfl

lemma charFun_defect_le_capped (μ : Measure ℝ) [IsProbabilityMeasure μ] (t a : ℝ) :
    1-(charFun μ t).re ≤ (t^2/2)*(∫ x, min (x^2) (a^2) ∂μ) +
      2*μ.real {x : ℝ | |a| < |x|} := by
  have hi : Integrable (fun x : ℝ => min (x^2) (a^2)) μ := by
    refine (integrable_const (a^2)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact min_le_right _ _)
  have hc : Integrable (fun x : ℝ => Real.cos (t*x)) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop)
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*x)))
  have hs : MeasurableSet {x : ℝ | |a| < |x|} := by measurability
  have hj : Integrable (Set.indicator {x : ℝ | |a| < |x|} (fun _ => (2:ℝ))) μ :=
    (integrable_const _).indicator hs
  have hm : (∫ x, 1-Real.cos (t*x) ∂μ) ≤
      ∫ x, (t^2/2)*min (x^2) (a^2) +
        Set.indicator {x : ℝ | |a| < |x|} (fun _ => (2:ℝ)) x ∂μ := by
    apply integral_mono ((integrable_const _).sub hc) ((hi.const_mul _).add hj)
    intro x
    simp only [Pi.sub_apply, Pi.add_apply]
    by_cases hx : |a| < |x|
    · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | |a| < |x|} from hx)]
      have := Real.neg_one_le_cos (t*x)
      have : 0 ≤ (t^2/2)*min (x^2) (a^2) := by positivity
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | |a| < |x|} from hx), add_zero, min_eq_left (sq_le_sq.mpr (le_of_not_gt hx))]
      have := Real.one_sub_sq_div_two_le_cos (x := t*x)
      nlinarith
  rw [integral_sub (integrable_const _) hc, integral_add (hi.const_mul _) hj,
    integral_const_mul, integral_indicator_const _ hs] at hm
  simpa only [integral_const, probReal_univ, one_smul, real_charFun, smul_eq_mul, mul_comm, mul_one] using hm

lemma exp_defect_lower (c z : ℝ) (hz : 0 ≤ z) (hzc : z ≤ c) :
    Real.exp (-c)*z ≤ 1-Real.exp (-z) := by
  have h1 := Real.add_one_le_exp z
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-z)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have h3 := Real.exp_le_exp.mpr (neg_le_neg hzc)
  nlinarith [mul_le_mul_of_nonneg_right h3 hz]

lemma exists_small_power (r k : ℝ) (hr : 0 < r) (hk : 0 < k) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d^r ≤ k := by
  refine ⟨min 1 (k^(1/r)), lt_min (by norm_num) (Real.rpow_pos_of_pos hk _), min_le_left _ _, ?_⟩
  calc
    (min 1 (k^(1/r)))^r ≤ (k^(1/r))^r :=
      Real.rpow_le_rpow (le_of_lt (lt_min (by norm_num) (Real.rpow_pos_of_pos hk _)))
        (min_le_right _ _) hr.le
    _ = k := by rw [← Real.rpow_mul hk.le, one_div_mul_cancel hr.ne', Real.rpow_one]

lemma stable_tail_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (hc : 0 < c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p)) :
    ∃ k : ℝ, 0 < k ∧ ∀ a : ℝ, 1 ≤ a → k*a^(-p) ≤ μ.real {x : ℝ | a < |x|} := by
  obtain ⟨d, hd, hd1, hdp⟩ := exists_small_power (2-p) (Real.exp (-c)/24) (by linarith) (by positivity)
  refine ⟨c*d^p*Real.exp (-c)/4, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have had : 0 ≤ d/a := by positivity
  have hda : d/a ≤ 1 := (div_le_one ha0).mpr (hd1.trans ha)
  have hpw : (d/a)^p ≤ 1 := by
    simpa using Real.rpow_le_rpow had hda hp.le
  have hz : 0 ≤ c*(d/a)^p := by positivity
  have hzc : c*(d/a)^p ≤ c := by nlinarith
  have he := exp_defect_lower c (c*(d/a)^p) hz hzc
  have hf := charFun_defect_le_capped μ (d/a) a
  rw [hcf, abs_of_nonneg had, abs_of_pos ha0] at hf
  have hs := stable_capped_second_upper μ p c hp hc.le hcf a ha0
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ (d/a)^2/2 by positivity)
  have haexp : (d/a)^2/2*(24*c*a^(2-p)) = 12*c*d^2*a^(-p) := by
    rw [div_pow]
    have heq : a^(2-p) = a^2*a^(-p) := by rw [sub_eq_add_neg, Real.rpow_add ha0, Real.rpow_two]
    rw [heq]
    field_simp
    ring
  rw [haexp] at hb
  have hdexp : d^2 = d^p*d^(2-p) := by rw [← Real.rpow_add hd, add_sub_cancel, Real.rpow_two]
  have hsmall : 12*c*d^2 ≤ c*d^p*Real.exp (-c)/2 := by
    rw [hdexp]
    nlinarith [mul_le_mul_of_nonneg_left hdp (show 0 ≤ 12*c*d^p by positivity)]
  have hpower : (d/a)^p = d^p*a^(-p) := by
    rw [Real.div_rpow hd.le ha0.le, Real.rpow_neg ha0.le]
    rfl
  rw [hpower] at he
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg ha0.le (-p))
  have harg : -c*(d/a)^p = -(c*(d/a)^p) := by ring
  rw [harg, hpower] at hf
  nlinarith

end SubpolynomialLp

end

end OAI
