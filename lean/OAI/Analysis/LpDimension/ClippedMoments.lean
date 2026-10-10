import OAI.Analysis.LpDimension.FourierTails

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uE uΩ

namespace SubpolynomialLp

lemma tail_measurable (μ : Measure ℝ) (f : ℝ → ℝ) :
    Measurable (fun t : ℝ => μ {x | t < f x}) :=
  Antitone.measurable (fun _ _ h => measure_mono (fun _ hx => lt_of_le_of_lt h hx))

lemma tail_real_measurable (μ : Measure ℝ) (f : ℝ → ℝ) :
    Measurable (fun t : ℝ => μ.real {x | t < f x}) :=
  (tail_measurable μ f).ennreal_toReal

lemma integral_power_derivative (q u : ℝ) (hq : 0 < q) (_hu : 0 ≤ u) :
    (∫ t in (0:ℝ)..u, q*t^(q-1)) = u^q := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < q-1)),
    sub_add_cancel, Real.zero_rpow hq.ne', sub_zero]
  field_simp

lemma capped_moment_layercake (μ : Measure ℝ) [IsFiniteMeasure μ]
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) :
    (∫ x, (min |x| a)^q ∂μ) =
      ∫ t in Set.Ioo (0:ℝ) a, (q*t^(q-1))*μ.real {x : ℝ | t < |x|} := by
  let f : ℝ → ℝ := fun x => min |x| a
  have hf : ∀ x, 0 ≤ f x := fun x => le_min (abs_nonneg x) ha.le
  have hfm : Measurable f := by fun_prop
  have hg : ∀ t > 0, IntervalIntegrable (fun t : ℝ => q*t^(q-1)) volume 0 t :=
    fun _ _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).const_mul q
  have hgn : ∀ᵐ t ∂volume.restrict (Set.Ioi (0:ℝ)), 0 ≤ q*t^(q-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hq.le (Real.rpow_nonneg (le_of_lt ht) _)
  have hk := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hf) hfm.aemeasurable hg hgn
  simp_rw [integral_power_derivative q _ hq (hf _)] at hk
  have hmeas : Measurable (fun t : ℝ => μ {x | t < f x} * ENNReal.ofReal (q*t^(q-1))) :=
    (tail_measurable μ f).mul (by fun_prop)
  have hfinite : ∀ᵐ t ∂volume.restrict (Set.Ioi (0:ℝ)),
      μ {x | t < f x} * ENNReal.ofReal (q*t^(q-1)) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top)
  calc
    (∫ x, (min |x| a)^q ∂μ) =
        (∫⁻ x, ENNReal.ofReal ((f x)^q) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => Real.rpow_nonneg (hf x) _)) (by fun_prop (disch := positivity))
    _ = (∫⁻ t in Set.Ioi (0:ℝ), μ {x | t < f x}*ENNReal.ofReal (q*t^(q-1))).toReal := by rw [hk]
    _ = ∫ t in Set.Ioi (0:ℝ), (q*t^(q-1))*μ.real {x | t < f x} := by
      rw [← integral_toReal hmeas.aemeasurable hfinite]
      apply integral_congr_ae
      filter_upwards [hgn] with t ht
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht, measureReal_def, mul_comm]
    _ = ∫ t in Set.Ioi (0:ℝ), (Set.Iio a).indicator
          (fun t => (q*t^(q-1))*μ.real {x : ℝ | t < |x|}) t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        dsimp only
        by_cases ht : t < a
        · rw [Set.indicator_of_mem (show t ∈ Set.Iio a from ht)]
          have he : {x | t < f x} = {x : ℝ | t < |x|} := by
            ext x
            simp [f, ht]
          rw [he]
        · rw [Set.indicator_of_notMem (show t ∉ Set.Iio a from ht)]
          have he : {x | t < f x} = ∅ := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            exact not_lt.mpr ((min_le_right |x| a).trans (le_of_not_gt ht))
          rw [he, measureReal_empty, mul_zero])
    _ = _ := by
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have he : Set.Iio a ∩ Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) a := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo, and_comm]
      rw [he]


lemma capped_moment_lower_log (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p k a : ℝ) (hp : 1 < p) (_hk : 0 ≤ k) (ha : 1 ≤ a)
    (htail : ∀ t : ℝ, 1 ≤ t → k*t^(-p) ≤ μ.real {x : ℝ | t < |x|}) :
    k*p*Real.log a ≤ ∫ x, (min |x| a)^p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [capped_moment_layercake μ p a (by linarith) ha0]
  let f : ℝ → ℝ := fun t => (p*t^(p-1))*μ.real {x : ℝ | t < |x|}
  have hf : IntegrableOn f (Set.Ioo 0 a) := by
    refine (((show Continuous (fun t : ℝ => p*t^(p-1)) by
      fun_prop (disch := linarith)).continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self).mono'
      (((by fun_prop : Measurable (fun t : ℝ => p*t^(p-1))).mul
        (tail_real_measurable μ (fun x => |x|))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    dsimp [f]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) measureReal_le_one
  have hsub : Set.Ioo (1:ℝ) a ⊆ Set.Ioo (0:ℝ) a :=
    fun _ ht => ⟨lt_trans zero_lt_one ht.1, ht.2⟩
  calc
    k*p*Real.log a = ∫ t in Set.Ioo (1:ℝ) a, (k*p)*t⁻¹ := by
      rw [integral_const_mul, integral_Ioc_eq_integral_Ioo.symm,
        ← intervalIntegral.integral_of_le ha, integral_inv_of_pos zero_lt_one ha0,
        div_one]
    _ ≤ ∫ t in Set.Ioo (1:ℝ) a, f t := by
      apply integral_mono_ae
        (((continuousOn_const.mul (continuousOn_inv₀.mono (fun t ht =>
          ne_of_gt (zero_lt_one.trans_le ht.1)))).integrableOn_Icc).mono_set
            Set.Ioo_subset_Icc_self) (hf.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      have he : (p*t^(p-1))*(k*t^(-p)) = (k*p)*t⁻¹ := by
        rw [mul_mul_mul_comm, ← Real.rpow_add ht0,
          show p-1+-p = -1 by ring, Real.rpow_neg_one, mul_comm p k]
      change (k*p)*t⁻¹ ≤ (p*t^(p-1))*μ.real {x : ℝ | t < |x|}
      rw [← he]
      exact mul_le_mul_of_nonneg_left (htail t ht.1.le) (by positivity)
    _ ≤ ∫ t in Set.Ioo (0:ℝ) a, f t := by
      apply setIntegral_mono_set hf
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        dsimp [f]
        exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1.le _))
          measureReal_nonneg
      · exact ae_of_all _ (fun _ h => hsub h)


lemma excess_first_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (p C a : ℝ) (hp : 1 < p) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ t : ℝ, 0 < t → μ.real {x : ℝ | t < |x|} ≤ C*t^(-p)) :
    Integrable (fun x : ℝ => max (|x|-a) 0) μ ∧
      (∫ x, max (|x|-a) 0 ∂μ) ≤ C*(1+1/(p-1))*a^(1-p) := by
  let f : ℝ → ℝ := fun x => max (|x|-a) 0
  have hf : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have hfm : Measurable f := by fun_prop
  have ht (t : ℝ) (ht : 0 < t) : {x | t < f x} = {x : ℝ | a+t < |x|} := by
    ext x
    simp only [Set.mem_ofPred_eq, f, lt_max_iff, not_lt.mpr ht.le, or_false]
    constructor <;> intro h <;> linarith
  have hbound (t : ℝ) (ht0 : 0 < t) :
      μ {x | t < f x} ≤ ENNReal.ofReal (C*(a+t)^(-p)) := by
    rw [ht t ht0, ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (htail (a+t) (add_pos ha ht0))
  have hdec {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : y^(-p) ≤ x^(-p) :=
    Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
  have h1 : (∫⁻ t in Set.Ioc (0:ℝ) a, μ {x | t < f x}) ≤ ENNReal.ofReal (C*a^(-p)*a) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioc (0:ℝ) a, ENNReal.ofReal (C*a^(-p)) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht'
        exact (hbound t ht'.1).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hdec ha (le_add_of_nonneg_right ht'.1.le)) hC))
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (mul_nonneg hC (by positivity))]
  have hi : IntegrableOn (fun t : ℝ => C*t^(-p)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) ha).const_mul C
  have h2 : (∫⁻ t in Set.Ioi a, μ {x | t < f x}) ≤ ENNReal.ofReal (C/(p-1)*a^(1-p)) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioi a, ENNReal.ofReal (C*t^(-p)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht'
        exact (hbound t (ha.trans ht')).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hdec (ha.trans ht') (le_add_of_nonneg_left ha.le)) hC))
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi]
        · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -p < -1) ha]
          congr 1
          rw [show -p+1 = -(p-1) by ring, neg_div_neg_eq, show -(p-1) = 1-p by ring]
          ring
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht'
          exact mul_nonneg hC (Real.rpow_nonneg (ha.trans ht').le _)
  have hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (C*(1+1/(p-1))*a^(1-p)) := by
    have he : Set.Ioi (0:ℝ) = Set.Ioc 0 a ∪ Set.Ioi a := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases ht' : t ≤ a
        · exact Or.inl ⟨h,ht'⟩
        · exact Or.inr (lt_of_not_ge ht')
      · intro h
        rcases h with h | h
        · exact h.1
        · exact ha.trans h
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hf) hfm.aemeasurable, he,
      lintegral_union measurableSet_Ioi (by exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h1.2 h2))]
    calc
      _ ≤ ENNReal.ofReal (C*a^(-p)*a) + ENNReal.ofReal (C/(p-1)*a^(1-p)) := add_le_add h1 h2
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hpow : a^(-p)*a = a^(1-p) := by
          calc
            _ = a^(-p)*a^(1:ℝ) := by rw [Real.rpow_one]
            _ = a^(1-p) := by rw [← Real.rpow_add ha]; congr 1; ring
        rw [mul_assoc, hpow]
        ring
  have hfi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable (ae_of_all _ hf)).mp
      (ne_of_lt (hlin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hfm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq
    (ENNReal.toReal_ofReal (by positivity))


def clip (a x : ℝ) : ℝ := max (-a) (min x a)

lemma clip_abs (a x : ℝ) (ha : 0 ≤ a) : |clip a x| = min |x| a := by
  unfold clip
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (le_trans (le_min hx ha) (le_max_right _ _)),
      max_eq_right (by exact le_trans (neg_nonpos.mpr ha) (le_min hx ha)), abs_of_nonneg hx]
  · rw [min_eq_left (hx.trans ha), abs_of_nonpos (max_le (neg_nonpos.mpr ha) hx), abs_of_nonpos hx]
    by_cases h : -a ≤ x
    · rw [max_eq_right h, min_eq_left (by linarith)]
    · rw [max_eq_left (le_of_not_ge h), min_eq_right (by linarith), neg_neg]

lemma clip_error (a x : ℝ) (ha : 0 ≤ a) : |x-clip a x| = max (|x|-a) 0 := by
  unfold clip
  rcases le_total x (-a) with hx | hx
  · rw [min_eq_left (hx.trans (by linarith)), max_eq_left hx,
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    ring
  · rcases le_total x a with hxa | hxa
    · rw [min_eq_left hxa, max_eq_right hx, sub_self, abs_zero,
        max_eq_right (by have := abs_le.mpr ⟨hx,hxa⟩; linarith)]
    · rw [min_eq_right hxa, max_eq_right (by linarith), abs_of_nonneg (sub_nonneg.mpr hxa),
        abs_of_nonneg (ha.trans hxa), max_eq_left (sub_nonneg.mpr hxa)]

lemma clip_measurable (a : ℝ) : Measurable (clip a) := by unfold clip; fun_prop

lemma capped_power_lipschitz (p a : ℝ) (hp : 1 ≤ p) (ha : 0 ≤ a) (x y : ℝ) :
    |(min |x| a)^p-(min |y| a)^p| ≤ p*a^(p-1)*|x-y| := by
  have hmem (x : ℝ) : min |x| a ∈ Set.Icc (0:ℝ) a :=
    ⟨le_min (abs_nonneg _) ha, min_le_right _ _⟩
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => t^p) (f' := fun t : ℝ => p*t^(p-1))
    (C := p*a^(p-1)) (fun t _ => (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1 _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith)) (by linarith))
    (convex_Icc (0:ℝ) a) (hmem y) (hmem x)
  simp only [Real.norm_eq_abs] at hm
  refine hm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (abs_min_sub_min_le_max |x| a |y| a).trans (by
    simp only [sub_self, abs_zero]
    exact max_le (abs_abs_sub_abs_le_abs_sub x y) (abs_nonneg _))

lemma capped_power_tail_bound (p a x : ℝ) (hp : 0 < p) (hp2 : p < 2) (ha : 0 < a) :
    0 ≤ |x|^p-(min |x| a)^p ∧ |x|^p-(min |x| a)^p ≤ a^(p-2)*x^2 := by
  have hn : (min |x| a)^p ≤ |x|^p :=
    Real.rpow_le_rpow (le_min (abs_nonneg _) ha.le) (min_le_left _ _) hp.le
  refine ⟨sub_nonneg.mpr hn, ?_⟩
  by_cases hx : |x| ≤ a
  · rw [min_eq_left hx, sub_self]
    positivity
  · have hx0 : 0 < |x| := ha.trans (lt_of_not_ge hx)
    have he : |x|^p = |x|^(p-2)*x^2 := by
      rw [← sq_abs x, ← Real.rpow_natCast |x| 2, ← Real.rpow_add hx0]
      congr 1
      norm_num
    calc
      |x|^p-(min |x| a)^p ≤ |x|^p := sub_le_self _ (Real.rpow_nonneg (le_min hx0.le ha.le) _)
      _ = |x|^(p-2)*x^2 := he
      _ ≤ a^(p-2)*x^2 := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha (le_of_not_ge hx) (by linarith)) (sq_nonneg _)


lemma bounded_power_integrable {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hm : Measurable f)
    (p K : ℝ) (hp : 0 < p) (_hK : 0 ≤ K) (hf : ∀ x, |f x| ≤ K) :
    Integrable (fun x => |f x|^p) μ := by
  refine (integrable_const (K^p)).mono' (by fun_prop (disch := positivity)) ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hf x) hp.le)

lemma bounded_capped_integrable {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hm : Measurable f)
    (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    Integrable (fun x => (min |f x| a)^p) μ := by
  refine (integrable_const (a^p)).mono' (by fun_prop (disch := positivity)) ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_min (abs_nonneg _) ha) _)]
    exact Real.rpow_le_rpow (le_min (abs_nonneg _) ha) (min_le_right _ _) hp.le)

lemma matrix_clip_bounds {E : Type uE} [Fintype E] (P : Matrix E E ℝ)
    (Y : E → ℝ) (T H : ℝ) (hT : 0 ≤ T)
    (hrow : ∀ e, (∑ f, |P e f|) ≤ H) (hPY : P.mulVec Y = Y) :
    (∀ e, |P.mulVec (fun f => clip T (Y f)) e| ≤ H*T) ∧
    (∀ e, |Y e-P.mulVec (fun f => clip T (Y f)) e| ≤
      ∑ f, |P e f| *max (|Y f|-T) 0) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · calc
      _ ≤ ∑ f, |P e f*clip T (Y f)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f, |P e f| *T := Finset.sum_le_sum (fun f _ => by
        rw [abs_mul, clip_abs T _ hT]
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg _))
      _ = (∑ f, |P e f|)*T := (Finset.sum_mul ..).symm
      _ ≤ H*T := mul_le_mul_of_nonneg_right (hrow e) hT
  · have he : Y e-P.mulVec (fun f => clip T (Y f)) e =
        ∑ f, P e f*(Y f-clip T (Y f)) := by
      rw [← congr_fun hPY e]
      change (∑ f, P e f*Y f)-(∑ f, P e f*clip T (Y f)) = _
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [he]
    simpa only [abs_mul, clip_error T _ hT] using Finset.abs_sum_le_sum_abs
      (fun f => P e f*(Y f-clip T (Y f))) Finset.univ

end SubpolynomialLp

end

end OAI
