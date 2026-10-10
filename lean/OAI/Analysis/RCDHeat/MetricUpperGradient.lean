import Mathlib
import OAI.Analysis.RCDHeat.HeatMetricSpeed

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: MetricUpperGradient, HeatLength, CountableMetricSpeed, MetricSpeedPointwise, MetricTwoSidedSpeed, HeatTwoSidedSpeed. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped Topology
 

 theorem dist_le_integral_of_ae_right_speed {Y : Type*} [PseudoMetricSpace Y]
    {c : ℝ → Y} {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : AbsolutelyContinuousOnInterval c a b)
    (hvint : IntervalIntegrable v volume a b)
    (hv : ∀ᵐ s : ℝ, s ∈ Ioo a b →
      Tendsto (fun t => dist (c s) (c t)/(t-s)) (𝓝[>] s) (𝓝 (v s))) :
    dist (c a) (c b) ≤ ∫s in a..b, v s := by
  let g := fun t => dist (c a) (c t)
  have hg : AbsolutelyContinuousOnInterval g a b := by
    apply absolutelyContinuous_of_dist_le hc
    exact fun s _ t _ => dist_dist_dist_le_right _ _ _
  have hder : ∀ᵐ s : ℝ, s ∈ Icc a b → deriv g s ≤ v s := by
    filter_upwards [hg.ae_differentiableAt,hv,(Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))]
      with s hs hvs heq hsa
    have hs' := hs (by simpa only [uIcc_of_le hab] using hsa)
    have hlimit := (hasDerivAt_iff_tendsto_slope_left_right.mp hs'.hasDerivAt).2
    apply le_of_tendsto_of_tendsto hlimit (hvs (heq.mpr hsa))
    filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
    simp only [slope_def_field]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr ht).le
    dsimp only [g]
    linarith [dist_triangle (c a) (c s) (c t)]
  have hh := intervalIntegral.integral_mono_ae_restrict hab hg.intervalIntegrable_deriv hvint
    ((ae_restrict_iff' measurableSet_Icc).mpr hder)
  rw [hg.integral_deriv_eq_sub] at hh
  simpa only [g,dist_self,sub_zero] using hh
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
 theorem intervalIntegrable_sqrt_nonneg {I : ℝ → ℝ} {a b : ℝ}
    (hI : IntervalIntegrable I volume a b) (h0 : ∀ s, 0 ≤ I s) :
    IntervalIntegrable (fun s => Real.sqrt (I s)) volume a b := by
  apply (hI.add (intervalIntegrable_const (c := (1:ℝ)))).mono_fun
  · exact hI.def'.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by linarith [h0 s] : 0 ≤ I s+1)]
    nlinarith [Real.sq_sqrt (h0 s),Real.sqrt_nonneg (I s),sq_nonneg (Real.sqrt (I s)-1)]
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 

 theorem NoncollapsedRCD.heat_fisher_length (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    letI := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
    ∀ (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
      (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
      (hfm : (∫x, f x ∂hausdorff n X) = 1), ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      dist (hX.heatProbability K n hn p f hf0 hfs hfm a)
        (hX.heatProbability K n hn p f hf0 hfs hfm b) ≤
          ∫s in a..b, Real.sqrt (fisherInformation (hausdorff n X) hX.quadratic f s).toReal := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC a b ha hab
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hI := heatAt_fisher_intervalIntegrable_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi
    hfr ha hab
  have hvint := intervalIntegrable_sqrt_nonneg hI (fun _ => ENNReal.toReal_nonneg)
  have hT : 0 < b+1 := by linarith
  have hc := hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC (b+1) hT.le
  have hc' := hc.mono (c := a) (d := b) (by
    rw [uIcc_of_le hab,uIcc_of_le hT.le]
    exact Icc_subset_Icc ha (by linarith : b ≤ b+1))
  apply dist_le_integral_of_ae_right_speed hab hc' hvint
  filter_upwards [hX.heat_right_transport_speed K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC (b+1) hT]
    with s hs
  intro hsa
  have hs0 : 0 < s := lt_of_le_of_lt ha hsa.1
  have hsb : s < b+1 := by linarith [hsa.2]
  have hv := (hs ⟨hs0,hsb⟩).2
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
  change Real.sqrt (wassersteinSq _ _).toReal/(t-s) =
    (wassersteinEDist (heatMeasure μ hX.quadratic (max s 0) f)
      (heatMeasure μ hX.quadratic (max t 0) f)).toReal/(t-s)
  rw [max_eq_left hs0.le,max_eq_left (hs0.le.trans ht.le),wassersteinEDist,
    ← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow]
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {Y : Type*} [PseudoMetricSpace Y]
 
noncomputable def countableMetricSpeed (c : ℝ → Y) (s : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, ENNReal.ofReal |deriv (fun t => dist (c t) (c (q:ℝ))) s|
 theorem countableMetricSpeed_measurable (c : ℝ → Y) : Measurable (countableMetricSpeed c) :=
  Measurable.iSup fun _ => (measurable_deriv _).abs.ennreal_ofReal
 theorem countableMetricSpeed_deriv_le {c : ℝ → Y} {s : ℝ}
    (hfin : countableMetricSpeed c s ≠ ∞) (q : ℚ) :
    |deriv (fun t => dist (c t) (c (q:ℝ))) s| ≤ (countableMetricSpeed c s).toReal := by
  have h := ENNReal.toReal_mono hfin (le_iSup
    (fun q : ℚ => ENNReal.ofReal |deriv (fun t => dist (c t) (c (q:ℝ))) s|) q)
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h
 theorem ac_distance_test {c : ℝ → Y} {a b : ℝ}
    (hc : AbsolutelyContinuousOnInterval c a b) (z : Y) :
    AbsolutelyContinuousOnInterval (fun t => dist (c t) z) a b := by
  apply absolutelyContinuous_of_dist_le hc
  exact fun s _ t _ => dist_dist_dist_le_left _ _ _
 theorem countableMetricSpeed_ae_le {c : ℝ → Y} {v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hv : ∀ᵐ s : ℝ, s ∈ Ioo a b →
      Tendsto (fun t => dist (c s) (c t)/(t-s)) (𝓝[>] s) (𝓝 (v s))) :
    ∀ᵐ s : ℝ, s ∈ Icc a b → countableMetricSpeed c s ≤ ENNReal.ofReal (v s) := by
  have hd : ∀ᵐ s : ℝ, ∀ q : ℚ, s ∈ uIcc a b →
      DifferentiableAt ℝ (fun t => dist (c t) (c (q:ℝ))) s :=
    ae_all_iff.mpr fun q => (ac_distance_test hc (c (q:ℝ))).ae_differentiableAt
  filter_upwards [hd,hv,(Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))]
    with s hds hvs heq hs
  apply iSup_le
  intro q
  apply ENNReal.ofReal_le_ofReal
  have hdq := ((hds q (by simpa only [uIcc_of_le hab] using hs)).hasDerivAt)
  have hl := ((hasDerivAt_iff_tendsto_slope_left_right.mp hdq).2).abs
  apply le_of_tendsto_of_tendsto hl (hvs (heq.mpr hs))
  filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
  have hts : s < t := ht
  simp only [slope_def_field,abs_div,abs_of_pos (sub_pos.mpr hts)]
  exact div_le_div_of_nonneg_right (by simpa only [dist_comm] using
      (abs_dist_sub_le (c t) (c s) (c (q:ℝ)))) (sub_pos.mpr ht).le
 theorem countableMetricSpeed_intervalIntegrable {c : ℝ → Y} {v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hvi : IntervalIntegrable v volume a b)
    (hv : ∀ᵐ s : ℝ, s ∈ Ioo a b →
      Tendsto (fun t => dist (c s) (c t)/(t-s)) (𝓝[>] s) (𝓝 (v s))) :
    IntervalIntegrable (fun s => (countableMetricSpeed c s).toReal) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply hvi.1.norm.mono' (countableMetricSpeed_measurable c).ennreal_toReal.aestronglyMeasurable
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [countableMetricSpeed_ae_le hab hc hv] with s hs hsa
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hs (Ioc_subset_Icc_self hsa))
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact hh.trans (by rw [ENNReal.toReal_ofReal']; exact max_le (le_abs_self _) (abs_nonneg _))
 theorem scalar_distance_le_integral_countableMetricSpeed {c : ℝ → Y} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hm : IntervalIntegrable (fun s => (countableMetricSpeed c s).toReal) volume a b)
    (hfin : ∀ᵐ s : ℝ, s ∈ Icc a b → countableMetricSpeed c s ≠ ∞)
    (q : ℚ) : |dist (c b) (c (q:ℝ))-dist (c a) (c (q:ℝ))| ≤
      ∫s in a..b, (countableMetricSpeed c s).toReal := by
  have hd := ac_distance_test hc (c (q:ℝ))
  rw [← hd.integral_deriv_eq_sub]
  apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
  apply intervalIntegral.integral_mono_ae_restrict hab hd.intervalIntegrable_deriv.abs hm
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hfin] with s hs hsa
  exact countableMetricSpeed_deriv_le (hs hsa) q
 theorem dist_le_of_rat_distance_test (c : ℝ → Y) {u w M : ℝ} (_huw : u ≤ w)
    (huC : ContinuousAt c u)
    (htest : ∀ q : ℚ, |dist (c w) (c (q:ℝ))-dist (c u) (c (q:ℝ))| ≤ M) :
    dist (c u) (c w) ≤ M := by
  obtain ⟨rs,hrs,hrL⟩ := mem_closure_iff_seq_limit.mp (Rat.denseRange_cast u)
  choose qs hqs using hrs
  have hrLC : Tendsto (fun i : ℕ => c (qs i : ℝ)) atTop (𝓝 (c u)) := by
    simpa only [hqs,Function.comp_def] using huC.tendsto.comp hrL
  have hh : Tendsto (fun i : ℕ => |dist (c w) (c (qs i : ℝ)) -
      dist (c u) (c (qs i : ℝ))|) atTop (𝓝 |dist (c w) (c u)-dist (c u) (c u)|) :=
    (((tendsto_const_nhds (x := c w)).dist hrLC).sub
      ((tendsto_const_nhds (x := c u)).dist hrLC)).abs
  have hl := le_of_tendsto hh (Eventually.of_forall fun i => htest (qs i))
  simpa only [dist_self,sub_zero,abs_of_nonneg dist_nonneg,dist_comm] using hl
 theorem dist_le_integral_countableMetricSpeed {c : ℝ → Y} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hm : IntervalIntegrable (fun s => (countableMetricSpeed c s).toReal) volume a b)
    (hfin : ∀ᵐ s : ℝ, s ∈ Icc a b → countableMetricSpeed c s ≠ ∞)
    {u w : ℝ} (hu : u ∈ Ioo a b) (hw : w ∈ Ioo a b) (huw : u ≤ w) :
    dist (c u) (c w) ≤ ∫s in u..w, (countableMetricSpeed c s).toReal := by
  have hsub : uIcc u w ⊆ uIcc a b := by
    rw [uIcc_of_le huw,uIcc_of_le hab]
    exact Icc_subset_Icc hu.1.le hw.2.le
  have hcc : AbsolutelyContinuousOnInterval c u w := hc.mono hsub
  have hmi : IntervalIntegrable (fun s => (countableMetricSpeed c s).toReal) volume u w := hm.mono_set hsub
  have hff : ∀ᵐ s : ℝ, s ∈ Icc u w → countableMetricSpeed c s ≠ ∞ := by
    filter_upwards [hfin] with s hs hsa
    exact hs ⟨hu.1.le.trans hsa.1,hsa.2.trans hw.2.le⟩
  have htest := scalar_distance_le_integral_countableMetricSpeed huw hcc hmi hff
  have hneigh : uIcc a b ∈ 𝓝 u := by
    rw [uIcc_of_le hab]
    exact Icc_mem_nhds hu.1 hu.2
  have huC : ContinuousAt c u := by
    rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
    have hh := (ac_distance_test hc (c u)).continuousOn.continuousAt hneigh
    simpa only [dist_self] using hh.tendsto
  exact dist_le_of_rat_distance_test c (u := u) (w := w)
    (M := ∫s in u..w, (countableMetricSpeed c s).toReal) huw huC htest

 
 theorem tendsto_metric_quotient_of_envelope {c : ℝ → Y} {s : ℝ} {P : ℝ → ℝ}
    (hfin : countableMetricSpeed c s ≠ ∞)
    (hd : ∀ q : ℚ, HasDerivAt (fun t => dist (c t) (c (q:ℝ)))
      (deriv (fun t => dist (c t) (c (q:ℝ))) s) s)
    (hP : HasDerivAt P (countableMetricSpeed c s).toReal s)
    (hbound : ∀ᶠ t in 𝓝 s, dist (c s) (c t) ≤ |P t-P s|) :
    Tendsto (fun t => dist (c s) (c t)/|t-s|) (𝓝[≠] s)
      (𝓝 (countableMetricSpeed c s).toReal) := by
  apply tendsto_order.mpr
  constructor
  · intro k hk
    by_cases hk0 : k < 0
    · exact Eventually.of_forall fun t => hk0.trans_le (div_nonneg dist_nonneg (abs_nonneg _))
    have hke : ENNReal.ofReal k < countableMetricSpeed c s :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt hk0) hfin).mpr hk
    obtain ⟨q,hq⟩ := lt_iSup_iff.mp hke
    have hkq : k < |deriv (fun t => dist (c t) (c (q:ℝ))) s| := by
      by_contra hn
      exact not_lt_of_ge (ENNReal.ofReal_le_ofReal (le_of_not_gt hn)) hq
    have hL := (hasDerivAt_iff_tendsto_slope.mp (hd q)).abs
    have hev := (tendsto_order.mp hL).1 k hkq
    filter_upwards [hev] with t ht
    apply ht.trans_le
    simp only [slope_def_field,abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    simpa only [dist_comm] using (abs_dist_sub_le (c t) (c s) (c (q:ℝ)))
  · intro k hk
    have hL := (hasDerivAt_iff_tendsto_slope.mp hP).abs
    rw [abs_of_nonneg ENNReal.toReal_nonneg] at hL
    have hev := (tendsto_order.mp hL).2 k hk
    filter_upwards [hev,hbound.filter_mono nhdsWithin_le_nhds] with t ht hb
    apply lt_of_le_of_lt _ ht
    simp only [slope_def_field,abs_div]
    exact div_le_div_of_nonneg_right hb (abs_nonneg _)

 
 theorem dist_le_abs_countableSpeed_primitive {c : ℝ → Y} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hm : IntervalIntegrable (fun s => (countableMetricSpeed c s).toReal) volume a b)
    (hfin : ∀ᵐ s : ℝ, s ∈ Icc a b → countableMetricSpeed c s ≠ ∞)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    dist (c s) (c t) ≤ |(∫r in a..t, (countableMetricSpeed c r).toReal)-
      (∫r in a..s, (countableMetricSpeed c r).toReal)| := by
  have has : IntervalIntegrable (fun r => (countableMetricSpeed c r).toReal) volume a s := by
    apply hm.mono_set
    rw [uIcc_of_le hs.1.le,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2.le
  have hat : IntervalIntegrable (fun r => (countableMetricSpeed c r).toReal) volume a t := by
    apply hm.mono_set
    rw [uIcc_of_le ht.1.le,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2.le
  rw [intervalIntegral.integral_interval_sub_left hat has]
  rcases le_total s t with hst | hts
  · exact (dist_le_integral_countableMetricSpeed hab hc hm hfin hs ht hst).trans (le_abs_self _)
  · calc
      dist (c s) (c t) = dist (c t) (c s) := dist_comm _ _
      _ ≤ ∫r in t..s, (countableMetricSpeed c r).toReal :=
        dist_le_integral_countableMetricSpeed hab hc hm hfin ht hs hts
      _ ≤ |∫r in t..s, (countableMetricSpeed c r).toReal| := le_abs_self _
      _ = |∫r in s..t, (countableMetricSpeed c r).toReal| := by
        rw [intervalIntegral.integral_symm,abs_neg]
 

 theorem ae_metric_speed_of_right_speed {c : ℝ → Y} {v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hvi : IntervalIntegrable v volume a b)
    (hv : ∀ᵐ s : ℝ, s ∈ Ioo a b →
      Tendsto (fun t => dist (c s) (c t)/(t-s)) (𝓝[>] s) (𝓝 (v s))) :
    ∀ᵐ s : ℝ, s ∈ Ioo a b →
      (countableMetricSpeed c s).toReal = v s ∧
      Tendsto (fun t => dist (c s) (c t)/|t-s|) (𝓝[≠] s) (𝓝 (v s)) := by
  have hm := countableMetricSpeed_intervalIntegrable hab hc hvi hv
  have hfin : ∀ᵐ s : ℝ, s ∈ Icc a b → countableMetricSpeed c s ≠ ∞ := by
    filter_upwards [countableMetricSpeed_ae_le hab hc hv] with s hs hsa
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hs hsa)
  have hd : ∀ᵐ s : ℝ, ∀ q : ℚ, s ∈ uIcc a b →
      DifferentiableAt ℝ (fun t => dist (c t) (c (q:ℝ))) s :=
    ae_all_iff.mpr fun q => (ac_distance_test hc (c (q:ℝ))).ae_differentiableAt
  filter_upwards [hfin,hd,hm.ae_hasDerivAt_integral,hv] with s hfs hds hps hvs hs
  have hsc : s ∈ uIcc a b := by simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self hs
  have ha : a ∈ uIcc a b := by simp only [uIcc_of_le hab,left_mem_Icc,hab]
  have hfull := tendsto_metric_quotient_of_envelope (hfs (Ioo_subset_Icc_self hs))
    (fun q => (hds q hsc).hasDerivAt) (hps hsc a ha) (by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      exact dist_le_abs_countableSpeed_primitive hab hc hm hfin hs ht)
  have hright : Tendsto (fun t => dist (c s) (c t)/(t-s)) (𝓝[>] s)
      (𝓝 (countableMetricSpeed c s).toReal) := by
    have hsub : Ioi s ⊆ {s}ᶜ := by
      intro t ht
      exact ne_of_gt ht
    apply (hfull.mono_left (nhdsWithin_mono s hsub)).congr'
    filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
    have hst : s < t := ht
    rw [abs_of_pos (sub_pos.mpr hst)]
  have heq := tendsto_nhds_unique hright (hvs hs)
  exact ⟨heq,by rwa [heq] at hfull⟩
 theorem ae_metric_derivative_of_right_speed {c : ℝ → Y} {v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hvi : IntervalIntegrable v volume a b)
    (hv : ∀ᵐ s : ℝ, s ∈ Ioo a b →
      Tendsto (fun t => dist (c s) (c t)/(t-s)) (𝓝[>] s) (𝓝 (v s))) :
    ∀ᵐ s : ℝ, s ∈ Ioo a b →
      Tendsto (fun t => dist (c s) (c t)/|t-s|) (𝓝[≠] s) (𝓝 (v s)) := by
  filter_upwards [ae_metric_speed_of_right_speed hab hc hvi hv] with s hs hsa
  exact (hs hsa).2
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 

 theorem NoncollapsedRCD.heat_probability_metric_speed (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    letI := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
    ∀ (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
      (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
      (hfm : (∫x, f x ∂hausdorff n X) = 1), ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ T : ℝ, 0 < T →
      let c := fun t => hX.heatProbability K n hn p f hf0 hfs hfm t
      ∀ᵐ s : ℝ, s ∈ Ioo 0 T →
        (countableMetricSpeed c s).toReal =
          Real.sqrt (fisherInformation (hausdorff n X) hX.quadratic f s).toReal ∧
        Tendsto (fun t => dist (c s) (c t)/|t-s|) (𝓝[≠] s)
          (𝓝 (Real.sqrt (fisherInformation (hausdorff n X) hX.quadratic f s).toReal)) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC T hT
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hI := heatAt_fisher_intervalIntegrable_nonneg μ hX.quadratic p hA hB hvol
    f hf0 hfi hfr (a := 0) le_rfl hT.le
  have hvint := intervalIntegrable_sqrt_nonneg hI (fun _ => ENNReal.toReal_nonneg)
  have hc := hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC T hT.le
  apply ae_metric_speed_of_right_speed hT.le hc hvint
  filter_upwards [hX.heat_right_transport_speed K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC T hT]
    with s hs hsa
  have hs0 := hsa.1
  have hv := (hs hsa).2
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
  change Real.sqrt (wassersteinSq _ _).toReal/(t-s) =
    (wassersteinEDist (heatMeasure μ hX.quadratic (max s 0) f)
      (heatMeasure μ hX.quadratic (max t 0) f)).toReal/(t-s)
  rw [max_eq_left hs0.le,max_eq_left (hs0.le.trans ht.le),wassersteinEDist,
    ← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow]

end RegularPointCoordinates

end OAI
