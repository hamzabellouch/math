import Mathlib
import OAI.Analysis.RCDHeat.MetricDescentSlope

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EntropyWassersteinGeodesic, EntropyDirectional, GeodesicWeakGradient, GeodesicIntegral, CompressionPullback, TestPlanMeasure. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem transportCost_plan_eq_integral (plan : Measure C(Time,X))
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) plan) :
    transportCost (plan.map (fun γ => (γ 0,γ 1))) =
      ENNReal.ofReal (∫γ, dist (γ 0) (γ 1)^2 ∂plan) := by
  rw [transportCost,lintegral_map
    ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2)
    ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
  rw [ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro γ
  exact (ENNReal.ofReal_pow dist_nonneg 2).symm
variable [StandardBorelSpace X]
 

 theorem FullCD.exists_entropy_wasserstein_geodesic (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀.AbsolutelyContinuous μ) (h₁ : ν₁.AbsolutelyContinuous μ)
    (hm₀ : FiniteSecondMoment ν₀) (hm₁ : FiniteSecondMoment ν₁)
    (hEnt₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (hEnt₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal) μ)
    (p : X) {a : ℝ} (ha : 0 ≤ a)
    (hneg : Integrable (fun x => Real.exp (-a*dist p x)) μ)
    (hexp₀ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₀)
    (hexp₁ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₁)
    (hd₀ : Integrable (fun x => dist p x^2) ν₀)
    (hd₁ : Integrable (fun x => dist p x^2) ν₁) :
    ∃ plan : Measure C(Time,X), IsProbabilityMeasure plan ∧
      (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
      plan.map (fun γ => γ 0) = ν₀ ∧ plan.map (fun γ => γ 1) = ν₁ ∧
      wassersteinSq ν₀ ν₁ ≠ ∞ ∧
      (∀ s t : Time, wassersteinEDist (plan.map (fun γ => γ s)) (plan.map (fun γ => γ t)) =
        ENNReal.ofReal |(s:ℝ)-(t:ℝ)| * wassersteinEDist ν₀ ν₁) ∧
      ∀ t : Time, let ν := plan.map (fun γ => γ t)
        ν.AbsolutelyContinuous μ ∧
        Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ ∧
        boltzmannEntropy μ ν ≤ (1-(t:ℝ))*boltzmannEntropy μ ν₀+
          (t:ℝ)*boltzmannEntropy μ ν₁+
          ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(wassersteinSq ν₀ ν₁).toReal := by
  let : Nonempty X := ⟨p⟩
  obtain ⟨plan,hp,hg,ho,hE⟩ := hcd.exists_finite_entropy_exp_plan μ K n ν₀ ν₁ h₀ h₁
    hm₀ hm₁ hEnt₀ hEnt₁ p ha hneg hexp₀ hexp₁ hd₀ hd₁
  let := hp
  obtain ⟨he0,he1⟩ := optimalPlan_endpoints ν₀ ν₁ plan ho
  have hi := optimalPlan_dist_sq_integrable ν₀ ν₁ plan ho p hd₀ hd₁
  have hcost := transportCost_plan_eq_integral plan hi
  have hcfin : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := hcost ▸ ENNReal.ofReal_ne_top
  have hW : wassersteinSq ν₀ ν₁ = ENNReal.ofReal (∫γ, dist (γ 0) (γ 1)^2 ∂plan) :=
    (wassersteinSq_eq_cost ho).trans hcost
  have hWR : (wassersteinSq ν₀ ν₁).toReal = ∫γ, dist (γ 0) (γ 1)^2 ∂plan := by
    rw [hW,ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))]
  refine ⟨plan,hp,hg,he0,he1,(wassersteinSq_eq_cost ho) ▸ hcfin,?_,?_⟩
  · intro s t
    have hop : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
        (plan.map (fun γ => (γ 0,γ 1))) := by simpa only [he0,he1] using ho
    simpa only [he0,he1] using wassersteinEDist_geodesic_plan plan hg hop hcfin s t
  · intro t
    simpa only [boltzmannEntropy,hWR] using hE t
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem entropy_plan_signed_secant (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (h0 : ν₀ ≪ μ) (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (φ : X → ℝ) {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hrep : φ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hmap0 : plan.map (fun γ => γ 0) = ν₀)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) plan)
    (K : ℝ) (t : Time) (ht : 0 < (t:ℝ))
    (hac : plan.map (fun γ => γ t) ≪ μ)
    (het : Integrable (fun x => ((plan.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((plan.map (fun γ => γ t)).rnDeriv μ x).toReal) μ)
    (hc : boltzmannEntropy μ (plan.map (fun γ => γ t)) ≤
      (1-(t:ℝ))*boltzmannEntropy μ ν₀+(t:ℝ)*boltzmannEntropy μ ν₁+
      ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan)) :
    (∫γ : C(Time,X), (φ (γ t)-φ (γ 0))/(t:ℝ) ∂plan) ≤
      boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
        (K*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan) := by
  let ν := plan.map (fun γ => γ t)
  let : IsProbabilityMeasure ν := inferInstance
  have hi0 : Integrable φ ν₀ :=
    ((integrable_toReal_rnDeriv_mul_iff h0).mp he0).congr (h0.ae_eq hrep).symm
  have hi0p : Integrable (fun γ : C(Time,X) => φ (γ 0)) plan := by
    rw [← hmap0] at hi0
    exact hi0.comp_measurable (measurable_path_eval 0)
  have hit : Integrable (fun γ : C(Time,X) => φ (γ t)) plan := by
    apply ((geodesic_increment_integrable plan hg φ hφ hD t).add hi0p).congr
    filter_upwards with γ
    exact sub_add_cancel _ _
  have hit' : Integrable φ ν :=
    (integrable_map_measure hφ.continuous.aestronglyMeasurable
      (measurable_path_eval t).aemeasurable).mpr hit
  have hs := entropy_subgradient_rep μ ν₀ ν h0 hac hpos he0 het φ hrep hit'
  have hI0 : (∫γ : C(Time,X), φ (γ 0) ∂plan) = ∫x, φ x ∂ν₀ := by
    rw [← hmap0,integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.aestronglyMeasurable]
  have hIt : (∫γ : C(Time,X), φ (γ t) ∂plan) = ∫x, φ x ∂ν :=
    (integral_map (measurable_path_eval t).aemeasurable hφ.continuous.aestronglyMeasurable).symm
  rw [integral_div,integral_sub hit hi0p,hI0,hIt]
  apply (div_le_iff₀ ht).mpr
  change boltzmannEntropy μ ν ≤ _ at hc
  nlinarith only [hs,hc]

 

 theorem FullCD.exists_entropy_directional_plan (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀ ≪ μ) (h₁ : ν₁ ≪ μ)
    (hm₀ : FiniteSecondMoment ν₀) (hm₁ : FiniteSecondMoment ν₁)
    (he₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (he₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal * Real.log (ν₁.rnDeriv μ x).toReal) μ)
    (p : X) {a : ℝ} (ha : 0 ≤ a)
    (hneg : Integrable (fun x => Real.exp (-a*dist p x)) μ)
    (hexp₀ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₀)
    (hexp₁ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₁)
    (hd₀ : Integrable (fun x => dist p x^2) ν₀)
    (hd₁ : Integrable (fun x => dist p x^2) ν₁)
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (φ : X → ℝ) {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hrep : φ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal) :
    ∃ plan : Measure C(Time,X), IsProbabilityMeasure plan ∧
      (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))) ∧
      ∀ t : Time, 0 < (t:ℝ) →
        (∫γ : C(Time,X), (φ (γ t)-φ (γ 0))/(t:ℝ) ∂plan) ≤
          boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
            (K*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan) := by
  obtain ⟨plan,hp,hg,hopt,hconv⟩ := hcd.exists_finite_entropy_exp_plan μ K n
    ν₀ ν₁ h₀ h₁ hm₀ hm₁ he₀ he₁ p ha hneg hexp₀ hexp₁ hd₀ hd₁
  let := hp
  have hD2 := optimalPlan_dist_sq_integrable ν₀ ν₁ plan hopt p hd₀ hd₁
  have hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) plan := by
    have hm : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 plan :=
      (memLp_two_iff_integrable_sq
        ((continuous_eval_const 0).dist (continuous_eval_const 1)).aestronglyMeasurable).mpr hD2
    exact hm.integrable (by norm_num)
  refine ⟨plan,hp,hg,hopt,fun t ht => ?_⟩
  obtain ⟨hac,het,hc⟩ := hconv t
  exact entropy_plan_signed_secant μ ν₀ ν₁ h₀ hpos he₀ φ hφ hrep plan hg
    (optimalPlan_endpoints ν₀ ν₁ plan hopt).1 hD K t ht hac het hc
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X]

 

 theorem norm_deriv_comp_le_localSlope {φ : X → ℝ} {C D : ℝ≥0}
    (hφ : LipschitzWith C φ) {c : ℝ → X} (hc : LipschitzWith D c) (t : ℝ) :
    ‖deriv (φ ∘ c) t‖ ≤ D * (localSlope φ (c t)).toReal := by
  have hnn : ENNReal.ofReal ‖deriv (φ ∘ c) t‖ ≤
      (D:ℝ≥0∞)*localSlope φ (c t) := by
    rw [localSlope_eq_iInf_scale]
    rw [ENNReal.mul_iInf (fun h => (ENNReal.coe_ne_top h).elim)]
    refine le_iInf fun j => ?_
    let r : ℝ := 1/(j+1:ℝ)
    have hr : 0 < r := by positivity
    change _ ≤ (D:ℝ≥0∞)*slopeAtScale φ r (c t)
    have hfin : slopeAtScale φ r (c t) ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (slopeAtScale_le_lipschitz hφ r (c t)) ENNReal.coe_lt_top)
    have hbound : ‖deriv (φ ∘ c) t‖ ≤ D*(slopeAtScale φ r (c t)).toReal := by
      apply norm_deriv_le_of_lip' (mul_nonneg D.coe_nonneg ENNReal.toReal_nonneg)
      have hnear : ∀ᶠ s in 𝓝 t, dist (c t) (c s) < r :=
        by
        have hh := hc.continuous.continuousAt.eventually (Metric.ball_mem_nhds (c t) hr)
        filter_upwards [hh] with s hs
        simpa only [Metric.mem_ball,dist_comm] using hs
      filter_upwards [hnear] with s hs
      simp only [Function.comp_apply,Real.norm_eq_abs]
      by_cases he : c s = c t
      · rw [he,sub_self,abs_zero]
        positivity
      have hq := (ENNReal.toReal_le_toReal (by finiteness) hfin).mpr
        (slopeAtScale_term_le φ hs he)
      rw [ENNReal.toReal_ofReal (by positivity)] at hq
      have hd : 0 < dist (c t) (c s) := dist_pos.mpr (Ne.symm he)
      have hab := (div_le_iff₀ hd).mp hq
      calc
        |φ (c s)-φ (c t)| ≤ (slopeAtScale φ r (c t)).toReal * dist (c t) (c s) := hab
        _ ≤ (slopeAtScale φ r (c t)).toReal * (D*|s-t|) := by
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          simpa only [Real.dist_eq,abs_sub_comm] using hc.dist_le_mul t s
        _ = D * (slopeAtScale φ r (c t)).toReal * |s-t| := by ring
    have he := ENNReal.ofReal_le_ofReal hbound
    rw [ENNReal.ofReal_mul D.coe_nonneg,ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal hfin] at he
    exact he
  have hfin := ne_of_lt (lt_of_le_of_lt (localSlope_le_of_lipschitz hφ (c t)) ENNReal.coe_lt_top)
  have hh := (ENNReal.toReal_le_toReal (by finiteness) (ENNReal.mul_ne_top (by finiteness) hfin)).mpr hnn
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,ENNReal.coe_toReal] using hh

noncomputable def geodesicExtension (γ : C(Time,X)) (t : ℝ) : X :=
  γ (Set.projIcc 0 1 zero_le_one t)

 theorem geodesicExtension_eq (γ : C(Time,X)) (t : Time) :
    geodesicExtension γ (t:ℝ) = γ t := by
  simp only [geodesicExtension,Set.projIcc_of_mem zero_le_one t.property]

 theorem IsGeodesic.extension_lipschitz {γ : C(Time,X)} (hγ : IsGeodesic γ) :
    LipschitzWith ⟨dist (γ 0) (γ 1),dist_nonneg⟩ (geodesicExtension γ) := by
  have h : LipschitzWith ⟨dist (γ 0) (γ 1),dist_nonneg⟩ γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hγ]
    simp only [Subtype.dist_eq,Real.dist_eq]
    exact (mul_comm _ _).le
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (γ (Set.projIcc 0 1 zero_le_one s))
      (γ (Set.projIcc 0 1 zero_le_one t)) ≤ _
  calc
    _ ≤ dist (γ 0) (γ 1) * dist (Set.projIcc 0 1 zero_le_one s)
        (Set.projIcc 0 1 zero_le_one t) := h.dist_le_mul _ _
    _ ≤ dist (γ 0) (γ 1) * dist s t := by
      apply mul_le_mul_of_nonneg_left _ dist_nonneg
      have hp := (LipschitzWith.projIcc (show (0:ℝ) ≤ 1 from zero_le_one)).dist_le_mul s t
      change _ ≤ (1:ℝ) * dist s t at hp
      exact hp.trans_eq (one_mul _)

end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 theorem localSlope_comp_intervalIntegrable {φ : X → ℝ} {C D : ℝ≥0}
    (hφ : LipschitzWith C φ) {c : ℝ → X} (hc : LipschitzWith D c) (a b : ℝ) :
    IntervalIntegrable (fun t => (localSlope φ (c t)).toReal) volume a b := by
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    (((localSlope_measurable hφ.continuous).comp hc.continuous.measurable).ennreal_toReal.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg,Real.norm_of_nonneg C.coe_nonneg]
  simpa only [ENNReal.coe_toReal,Function.comp_apply] using ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_of_lipschitz hφ (c t))

 

 theorem lipschitz_increment_le_integral_localSlope {φ : X → ℝ} {C D : ℝ≥0}
    (hφ : LipschitzWith C φ) {c : ℝ → X} (hc : LipschitzWith D c)
    {a b : ℝ} (hab : a ≤ b) :
    |φ (c b)-φ (c a)| ≤ D*(∫ t in a..b, (localSlope φ (c t)).toReal) := by
  have hac : AbsolutelyContinuousOnInterval (φ ∘ c) a b :=
    (hφ.comp hc).lipschitzOnWith.absolutelyContinuousOnInterval
  have hi := localSlope_comp_intervalIntegrable hφ hc a b
  calc
    |φ (c b)-φ (c a)| = ‖∫t in a..b, deriv (φ ∘ c) t‖ := by
      rw [hac.integral_deriv_eq_sub]
      rfl
    _ ≤ ∫t in a..b, ‖deriv (φ ∘ c) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫t in a..b, (D:ℝ)*(localSlope φ (c t)).toReal := by
      apply intervalIntegral.integral_mono hab hac.intervalIntegrable_deriv.norm (hi.const_mul _)
      exact norm_deriv_comp_le_localSlope hφ hc
    _ = _ := intervalIntegral.integral_const_mul _ _

 theorem IsGeodesic.increment_le_integral_localSlope {γ : C(Time,X)} (hγ : IsGeodesic γ)
    {φ : X → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {a b : Time} (hab : (a:ℝ) ≤ (b:ℝ)) :
    |φ (γ b)-φ (γ a)| ≤ dist (γ 0) (γ 1)*
      (∫t in (a:ℝ)..(b:ℝ), (localSlope φ (geodesicExtension γ t)).toReal) := by
  have h := lipschitz_increment_le_integral_localSlope hφ hγ.extension_lipschitz hab
  change |φ (geodesicExtension γ (b:ℝ))-φ (geodesicExtension γ (a:ℝ))| ≤
    dist (γ 0) (γ 1) * _ at h
  rw [geodesicExtension_eq,geodesicExtension_eq] at h
  exact h

end

 
section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

 

noncomputable def compressionPullback (μ : Measure α) (ν : Measure β)
    (e : β → α) (he : Measurable e) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ν.map e ≤ C • μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  ((Lp.compMeasurePreservingₗᵢ ℝ e ⟨he,rfl⟩).toContinuousLinearMap).comp
    (Lp.LpToLpOfMeasureLeSMul hC hcomp)

 theorem compressionPullback_ae (μ : Measure α) (ν : Measure β)
    (e : β → α) (he : Measurable e) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ν.map e ≤ C • μ) (f : Lp ℝ 2 μ) :
    ⇑(compressionPullback μ ν e he hC hcomp f) =ᵐ[ν] fun y => f (e y) := by
  have hh := Lp.coeFn_LpToLpOfMeasureLeSMul hC hcomp f
  have hh' := ae_of_ae_map he.aemeasurable hh
  have ha := Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul hC hcomp f) (show MeasurePreserving e ν (ν.map e) from ⟨he,rfl⟩)
  exact ha.trans hh'

 theorem compressionPullback_tendsto (μ : Measure α) (ν : Measure β)
    (e : β → α) (he : Measurable e) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ν.map e ≤ C • μ) {fs : ℕ → Lp ℝ 2 μ} {f : Lp ℝ 2 μ}
    (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun i => compressionPullback μ ν e he hC hcomp (fs i)) atTop
      (𝓝 (compressionPullback μ ν e he hC hcomp f)) :=
  (compressionPullback μ ν e he hC hcomp).continuous.continuousAt.tendsto.comp hf

 theorem compressionPullback_memLp (μ : Measure α) (ν : Measure β)
    (e : β → α) (he : Measurable e) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ν.map e ≤ C • μ) (f : Lp ℝ 2 μ) :
    MemLp (fun y => f (e y)) 2 ν :=
  ((Lp.memLp f).of_measure_le_smul hC hcomp).comp_of_map he.aemeasurable

end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def testPlanMeasure (π : Measure C(Time,X)) : Measure (ℝ × C(Time,X)) :=
  (volume.restrict (Icc (0:ℝ) 1)).prod π
noncomputable def testPlanEval (z : ℝ × C(Time,X)) : X := geodesicExtension z.2 z.1

omit [MeasurableSpace X] [BorelSpace X] in
 theorem testPlanEval_continuous : Continuous (testPlanEval (X := X)) := by
  exact continuous_eval.comp (continuous_snd.prodMk
    ((LipschitzWith.projIcc (show (0:ℝ) ≤ 1 from zero_le_one)).continuous.comp continuous_fst))

 theorem testPlanEval_measurable : Measurable (testPlanEval (X := X)) :=
  testPlanEval_continuous.measurable

 

 theorem testPlanMeasure_compression (μ : Measure X) (π : Measure C(Time,X)) [SFinite π]
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) :
    (testPlanMeasure π).map testPlanEval ≤ C • μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply testPlanEval_measurable hs]
  change ((volume.restrict (Icc (0:ℝ) 1)).prod π) (testPlanEval ⁻¹' s) ≤ _
  rw [Measure.prod_apply (testPlanEval_measurable hs)]
  calc
    _ ≤ ∫⁻ t : ℝ, (C • μ) s ∂(volume.restrict (Icc (0:ℝ) 1)) := by
      apply lintegral_mono
      intro t
      have ht := (hcomp (Set.projIcc 0 1 zero_le_one t)) s
      rw [Measure.map_apply (measurable_path_eval _) hs] at ht
      exact ht
    _ = (C • μ) s := by simp [Real.volume_Icc]

 theorem testPlanMeasure_eval_memLp (μ : Measure X) (π : Measure C(Time,X)) [SFinite π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (f : Lp ℝ 2 μ) :
    MemLp (fun z : ℝ × C(Time,X) => f (testPlanEval z)) 2 (testPlanMeasure π) :=
  compressionPullback_memLp μ (testPlanMeasure π) testPlanEval testPlanEval_measurable
    hC (testPlanMeasure_compression μ π hcomp) f


end RegularPointCoordinates

end OAI
