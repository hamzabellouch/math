import Mathlib
import OAI.Analysis.RCDHeat.MetricUpperGradient
import OAI.Analysis.RCDHeat.ProbabilityCutoff

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: MetricDescentSlope, HeatFullSlope, HeatFullDissipation, HeatEDE, WassersteinGeodesic. -/



namespace RegularPointCoordinates

section
open Set Filter
open scoped ENNReal NNReal Topology
 

noncomputable def descentSlope {α : Type*} (d : α → α → ℝ) (E : α → ℝ)
    (D : Set α) (x : α) : ℝ≥0∞ :=
  ⨅ r : ℝ, ⨅ (_ : 0 < r), ⨆ y ∈ D, ⨆ (_ : 0 < d x y), ⨆ (_ : d x y < r),
    ENNReal.ofReal ((E x-E y)/d x y)
 theorem descentSlope_le_quadratic {α : Type*} {d : α → α → ℝ} {E : α → ℝ}
    {D : Set α} {x : α} {L C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y ∈ D, E x-E y ≤ L*d x y+C*(d x y)^2) :
    descentSlope d E D x ≤ ENNReal.ofReal L := by
  have hb (r : ℝ) (hr : 0 < r) : descentSlope d E D x ≤ ENNReal.ofReal (L+C*r) := by
    apply iInf_le_of_le r
    apply iInf_le_of_le hr
    refine iSup_le fun y => iSup_le fun hy => iSup_le fun hd => iSup_le fun hdr => ?_
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hd).mpr
    have hh := h y hy
    have hc := mul_le_mul_of_nonneg_left hdr.le hC
    nlinarith
  have hl : Tendsto (fun r : ℝ => ENNReal.ofReal (L+C*r)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal L)) := by
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero,add_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := L)).add (hr.const_mul C))
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with r hr
  exact hb r hr

 

 theorem le_descentSlope_of_right_speed {α : Type*} {d : α → α → ℝ} {E : α → ℝ}
    {D : Set α} {c : ℝ → α} {s L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ᶠ t in 𝓝[>] s, c t ∈ D)
    (hE : HasDerivAt (fun t => E (c t)) (-L^2) s)
    (hv : Tendsto (fun t => d (c s) (c t)/(t-s)) (𝓝[>] s) (𝓝 L)) :
    ENNReal.ofReal L ≤ descentSlope d E D (c s) := by
  rcases eq_or_lt_of_le hL with hl | hl
  · simp only [← hl,ENNReal.ofReal_zero,zero_le]
  have ht : ∀ᶠ t in 𝓝[>] s, s < t := self_mem_nhdsWithin
  have hδ : Tendsto (fun t : ℝ => t-s) (𝓝[>] s) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).mono_left nhdsWithin_le_nhds).sub_const s
  have hdpos : ∀ᶠ t in 𝓝[>] s, 0 < d (c s) (c t) := by
    filter_upwards [ht,hv.eventually (lt_mem_nhds hl)] with t ht hp
    simpa only [zero_mul] using (lt_div_iff₀ (sub_pos.mpr ht)).mp hp
  have hd : Tendsto (fun t => d (c s) (c t)) (𝓝[>] s) (𝓝 0) := by
    have hh := hv.mul hδ
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [ht] with t ht
    exact div_mul_cancel₀ _ (sub_pos.mpr ht).ne'
  have henergy : Tendsto (fun t => (E (c s)-E (c t))/(t-s)) (𝓝[>] s) (𝓝 (L^2)) := by
    have hh := (hasDerivAt_iff_tendsto_slope_left_right.mp hE).2.neg
    convert! hh using 1
    · ext t
      simp only [slope_def_field]
      ring
    · simp
  have hratio : Tendsto (fun t => (E (c s)-E (c t))/d (c s) (c t))
      (𝓝[>] s) (𝓝 L) := by
    have hh := henergy.div hv hl.ne'
    have heq : L^2/L = L := by field_simp
    rw [heq] at hh
    apply hh.congr'
    filter_upwards [ht,hdpos] with t ht hp
    dsimp only [Pi.div_apply]
    field_simp [(sub_pos.mpr ht).ne',hp.ne']
  apply le_iInf fun r => le_iInf fun hr => ?_
  have hbound : ∀ᶠ t in 𝓝[>] s,
      ENNReal.ofReal ((E (c s)-E (c t))/d (c s) (c t)) ≤
        ⨆ y ∈ D, ⨆ (_ : 0 < d (c s) y), ⨆ (_ : d (c s) y < r),
          ENNReal.ofReal ((E (c s)-E y)/d (c s) y) := by
    filter_upwards [hD,hdpos,hd.eventually (gt_mem_nhds hr)] with t hDt hp htr
    exact le_iSup_of_le (c t) (le_iSup_of_le hDt (le_iSup_of_le hp (le_iSup_of_le htr le_rfl)))
  exact le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hratio) hbound
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 
def finiteEntropyDomain (μ : Measure X) : Set (Measure X) :=
  {ν | IsProbabilityMeasure ν ∧ ν ≪ μ ∧ FiniteSecondMoment ν ∧
    Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ}
 

 theorem NoncollapsedRCD.heat_finite_entropy_slope (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ T : ℝ, 0 < T →
      let μ := hausdorff n X
      let ρ := fun t => heatMeasure μ hX.quadratic t f
      ∀ᵐ s : ℝ, s ∈ Ioo 0 T →
        descentSlope (fun ν σ => (wassersteinEDist ν σ).toReal)
          (boltzmannEntropy μ) (finiteEntropyDomain μ) (ρ s) =
            ENNReal.ofReal (Real.sqrt (fisherInformation μ hX.quadratic f s).toReal) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC T hT
  change ∀ᵐ s : ℝ, s ∈ Ioo 0 T → _
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  let : NeZero μ := ⟨by
    intro hz
    have hh := hfm
    change (∫x, f x ∂μ) = 1 at hh
    rw [hz] at hh
    simp at hh⟩
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hspeed := hX.heat_right_transport_speed K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC T hT
  have hder := heatAt_entropy_ae_hasDerivAt_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi
    hfr le_rfl hT.le
  filter_upwards [hspeed,hder] with s hspeed hsder
  intro hs
  obtain ⟨hIs,hv⟩ := hspeed hs
  apply le_antisymm
  · apply descentSlope_le_quadratic (hC := (by positivity : 0 ≤ |K|/2))
    intro ν hν
    obtain ⟨hp,ha,hm,hE⟩ := hν
    let := hp
    exact hX.cd.heat_wasserstein_HWI_finite μ hX.quadratic K n p hA hB hvol f hf0 hfm hfr C
      (hfC.mono fun _ hx => (le_abs_self _).trans hx) hs.1 hIs ν ha hE
      (hm.integrable_dist_sq p)
  · apply le_descentSlope_of_right_speed (c := fun t => heatMeasure μ hX.quadratic t f)
      (Real.sqrt_nonneg _)
    · filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
      have ht0 : 0 ≤ t := hs.1.le.trans ht.le
      exact hX.heat_law K n hn p f hf0 ⟨r,hfr⟩ hfm t ht0
    · change HasDerivAt (fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f))
        (-(Real.sqrt (fisherInformation μ hX.quadratic f s).toReal)^2) s
      simpa only [boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0,
        Real.sq_sqrt ENNReal.toReal_nonneg] using hsder hs
    · simpa only [wassersteinEDist,← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow] using hv

 
 theorem NoncollapsedRCD.heat_full_slope_dissipation (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      let μ := hausdorff n X
      let ρ := fun t => heatMeasure μ hX.quadratic t f
      let S := fun t => (descentSlope (fun ν σ => (wassersteinEDist ν σ).toReal)
        (boltzmannEntropy μ) (finiteEntropyDomain μ) (ρ t)).toReal
      IntervalIntegrable (fun t => S t^2) volume a b ∧
        boltzmannEntropy μ (ρ b)+(∫t in a..b, S t^2) = boltzmannEntropy μ (ρ a) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC a b ha hab
  change IntervalIntegrable _ _ _ _ ∧ _
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hI := heatAt_fisher_intervalIntegrable_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr ha hab
  have hT : 0 < b+1 := by linarith
  have hS := hX.heat_finite_entropy_slope K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC (b+1) hT
  have heq : ∀ᵐ t : ℝ, t ∈ uIoc a b →
      (descentSlope (fun ν σ => (wassersteinEDist ν σ).toReal)
        (boltzmannEntropy μ) (finiteEntropyDomain μ) (heatMeasure μ hX.quadratic t f)).toReal^2 =
      (fisherInformation μ hX.quadratic f t).toReal := by
    filter_upwards [hS] with t ht hta
    rw [uIoc_of_le hab] at hta
    have ht0 : 0 < t := lt_of_le_of_lt ha hta.1
    have htb : t < b+1 := by linarith [hta.2]
    rw [ht ⟨ht0,htb⟩,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt ENNReal.toReal_nonneg]
  constructor
  · apply hI.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [heq] with t ht hta
    exact (ht hta).symm
  · rw [intervalIntegral.integral_congr_ae heq]
    have hh := heatAt_fisher_integral_entropy_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr ha hab
    change boltzmannEntropy μ (heatMeasure μ hX.quadratic b f)+
      (∫t in a..b, (fisherInformation μ hX.quadratic f t).toReal) =
        boltzmannEntropy μ (heatMeasure μ hX.quadratic a f)
    simp only [boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0]
    linarith

 
 theorem NoncollapsedRCD.heat_entropy_EDE (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
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
      let μ := hausdorff n X
      let c := fun t => hX.heatProbability K n hn p f hf0 hfs hfm t
      let ρ := fun t => heatMeasure μ hX.quadratic t f
      let speed := fun t => (countableMetricSpeed c t).toReal
      let S := fun t => (descentSlope (fun ν σ => (wassersteinEDist ν σ).toReal)
        (boltzmannEntropy μ) (finiteEntropyDomain μ) (ρ t)).toReal
      AbsolutelyContinuousOnInterval c 0 T ∧
      (∀ᵐ s : ℝ, s ∈ Ioo 0 T →
        Tendsto (fun t => dist (c s) (c t)/|t-s|) (𝓝[≠] s) (𝓝 (speed s))) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
        IntervalIntegrable (fun t => speed t^2) volume a b ∧
        IntervalIntegrable (fun t => S t^2) volume a b ∧
        boltzmannEntropy μ (ρ b)+(1/2)*(∫t in a..b, speed t^2)+
          (1/2)*(∫t in a..b, S t^2) = boltzmannEntropy μ (ρ a) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC T hT
  let c := fun t => hX.heatProbability K n hn p f hf0 hfs hfm t
  let v := fun t => (countableMetricSpeed c t).toReal
  change AbsolutelyContinuousOnInterval c 0 T ∧ _
  have hspeed := hX.heat_probability_metric_speed K n hn p f hf0 hfs hfm C hfC T hT
  refine ⟨hX.heat_probability_absolutelyContinuous K n hn p f hf0 hfs hfm C hfC T hT.le,?_,?_⟩
  · filter_upwards [hspeed] with s hs hsa
    have hh := hs hsa
    rw [← hh.1] at hh
    exact hh.2
  · intro a b ha hab hbT
    change IntervalIntegrable (fun t => v t^2) volume a b ∧ _
    obtain ⟨r,hfr⟩ := hfs
    obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
    have hfi := lp_integrable_of_bounded_support μ f p hfr
    have hI := heatAt_fisher_intervalIntegrable_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr ha hab
    have hev : ∀ᵐ t : ℝ, t ∈ uIoc a b → v t^2 =
        (fisherInformation μ hX.quadratic f t).toReal := by
      filter_upwards [hspeed,(Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b))] with t ht heq hta
      rw [uIoc_of_le hab] at hta
      have htab : t ∈ Ioo a b := heq.mpr hta
      have htT : t ∈ Ioo 0 T := ⟨lt_of_le_of_lt ha htab.1,lt_of_lt_of_le htab.2 hbT⟩
      change (countableMetricSpeed c t).toReal^2 = _
      rw [(ht htT).1,Real.sq_sqrt ENNReal.toReal_nonneg]
    have hvi : IntervalIntegrable (fun t => v t^2) volume a b := by
      apply hI.congr_ae
      apply (ae_restrict_iff' measurableSet_uIoc).mpr
      filter_upwards [hev] with t ht hta
      exact (ht hta).symm
    have hD := hX.heat_full_slope_dissipation K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC a b ha hab
    refine ⟨hvi,hD.1,?_⟩
    have hEI := heatAt_fisher_integral_entropy_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr ha hab
    have hEI' : boltzmannEntropy μ (heatMeasure μ hX.quadratic b f)+
        (∫t in a..b, (fisherInformation μ hX.quadratic f t).toReal) =
        boltzmannEntropy μ (heatMeasure μ hX.quadratic a f) := by
      simp only [boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0]
      linarith
    have hvI := intervalIntegral.integral_congr_ae hev
    change boltzmannEntropy μ (heatMeasure μ hX.quadratic b f)+(1/2)*(∫t in a..b, v t^2)+
      (1/2)*(∫t in a..b, (descentSlope (fun ν σ => (wassersteinEDist ν σ).toReal)
        (boltzmannEntropy μ) (finiteEntropyDomain μ) (heatMeasure μ hX.quadratic t f)).toReal^2) =
        boltzmannEntropy μ (heatMeasure μ hX.quadratic a f)
    have hD' := hD.2
    change boltzmannEntropy μ (heatMeasure μ hX.quadratic b f)+_ =
      boltzmannEntropy μ (heatMeasure μ hX.quadratic a f) at hD'
    linarith
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem geodesic_plan_cost_root (plan : Measure C(Time,X))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ) (s t : Time) :
    transportCost (plan.map (fun γ => (γ s,γ t))) ^ (1/(2:ℝ)) =
      ENNReal.ofReal |(s:ℝ)-(t:ℝ)| *
        transportCost (plan.map (fun γ => (γ 0,γ 1))) ^ (1/(2:ℝ)) := by
  simp only [transportCost_sqrt_eq_eLpNorm]
  rw [eLpNorm_map_measure (measurable_fst.dist measurable_snd).aestronglyMeasurable
    ((measurable_path_eval s).prodMk (measurable_path_eval t)).aemeasurable,
    eLpNorm_map_measure (measurable_fst.dist measurable_snd).aestronglyMeasurable
    ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable]
  have hh : (fun γ : C(Time,X) => dist (γ s) (γ t)) =ᵐ[plan]
      |(s:ℝ)-(t:ℝ)| • (fun γ : C(Time,X) => dist (γ 0) (γ 1)) := by
    filter_upwards [hg] with γ hγ
    exact hγ s t
  change eLpNorm (fun γ : C(Time,X) => dist (γ s) (γ t)) 2 plan = _
  rw [eLpNorm_congr_ae hh,eLpNorm_const_smul,Real.enorm_eq_ofReal (abs_nonneg _)]
  rfl
 theorem wassersteinEDist_plan_le (plan : Measure C(Time,X))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hopt : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1)))) (s t : Time) :
    wassersteinEDist (plan.map (fun γ => γ s)) (plan.map (fun γ => γ t)) ≤
      ENNReal.ofReal |(s:ℝ)-(t:ℝ)| *
        wassersteinEDist (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1)) := by
  have h0 : (plan.map (fun γ => (γ s,γ t))).map Prod.fst = plan.map (fun γ => γ s) := by
    rw [Measure.map_map measurable_fst ((measurable_path_eval s).prodMk (measurable_path_eval t))]
    rfl
  have h1 : (plan.map (fun γ => (γ s,γ t))).map Prod.snd = plan.map (fun γ => γ t) := by
    rw [Measure.map_map measurable_snd ((measurable_path_eval s).prodMk (measurable_path_eval t))]
    rfl
  calc
    _ ≤ _ := wassersteinEDist_le_cost h0 h1
    _ = _ := by rw [geodesic_plan_cost_root plan hg s t,wassersteinEDist,wassersteinSq_eq_cost hopt]
variable [StandardBorelSpace X] [Nonempty X]
 

 theorem wassersteinEDist_geodesic_plan (plan : Measure C(Time,X)) [IsFiniteMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hopt : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞) (s t : Time) :
    wassersteinEDist (plan.map (fun γ => γ s)) (plan.map (fun γ => γ t)) =
      ENNReal.ofReal |(s:ℝ)-(t:ℝ)| *
        wassersteinEDist (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1)) := by
  let ν := fun t : Time => plan.map (fun γ => γ t)
  let D := wassersteinEDist (ν 0) (ν 1)
  have hD : D ≠ ∞ := by
    dsimp [D,wassersteinEDist,ν]
    rw [wassersteinSq_eq_cost hopt]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin
  have hup (a b : Time) : wassersteinEDist (ν a) (ν b) ≤ ENNReal.ofReal |(a:ℝ)-(b:ℝ)| * D :=
    wassersteinEDist_plan_le plan hg hopt a b
  have hlo (a b : Time) (hab : a ≤ b) :
      ENNReal.ofReal |(a:ℝ)-(b:ℝ)| * D ≤ wassersteinEDist (ν a) (ν b) := by
    have hab' : (a:ℝ) ≤ (b:ℝ) := hab
    have hdec : D = ENNReal.ofReal (a:ℝ)*D+
        ENNReal.ofReal ((b:ℝ)-(a:ℝ))*D+ENNReal.ofReal (1-(b:ℝ))*D := by
      rw [← add_mul,← add_mul,← ENNReal.ofReal_add a.2.1 (sub_nonneg.mpr hab'),
        ← ENNReal.ofReal_add (by linarith [a.2.1]) (sub_nonneg.mpr b.2.2)]
      have he : (a:ℝ)+((b:ℝ)-(a:ℝ))+(1-(b:ℝ)) = 1 := by ring
      rw [he,ENNReal.ofReal_one,one_mul]
    have htri : D ≤ ENNReal.ofReal (a:ℝ)*D+wassersteinEDist (ν a) (ν b)+
        ENNReal.ofReal (1-(b:ℝ))*D := by
      calc
        D ≤ wassersteinEDist (ν 0) (ν a)+wassersteinEDist (ν a) (ν 1) :=
          wassersteinEDist_triangle _ _ _
        _ ≤ wassersteinEDist (ν 0) (ν a)+
            (wassersteinEDist (ν a) (ν b)+wassersteinEDist (ν b) (ν 1)) :=
          add_le_add le_rfl (wassersteinEDist_triangle _ _ _)
        _ ≤ _ := by
          have ha := hup 0 a
          have hb := hup b 1
          change wassersteinEDist (ν 0) (ν a) ≤ ENNReal.ofReal |0-(a:ℝ)| * D at ha
          change wassersteinEDist (ν b) (ν 1) ≤ ENNReal.ofReal |(b:ℝ)-1| * D at hb
          simp only [zero_sub,abs_neg,abs_of_nonneg a.2.1] at ha
          rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr b.2.2)] at hb
          simpa only [add_assoc] using add_le_add (add_le_add ha le_rfl) hb
    conv_lhs at htri => rw [hdec]
    have hf (c : ℝ) : ENNReal.ofReal c*D ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD
    have hh := (ENNReal.add_le_add_iff_right (hf (1-(b:ℝ)))).mp htri
    have hh' := (ENNReal.add_le_add_iff_left (hf (a:ℝ))).mp hh
    simpa only [abs_sub_comm (a:ℝ),abs_of_nonneg (sub_nonneg.mpr hab')] using hh'
  apply le_antisymm (hup s t)
  rcases le_total s t with hst | hts
  · exact hlo s t hst
  · rw [wassersteinEDist_symm,abs_sub_comm]
    exact hlo t s hts

end RegularPointCoordinates

end OAI
