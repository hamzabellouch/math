import Mathlib
import OAI.Analysis.RCDHeat.WeightedMoment

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedPlan, EntropySubgradient, GeodesicSlope, GeodesicIntegralSlope, EntropyGeodesic. -/



namespace RegularPointCoordinates

section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem optimalPlan_dist_sq_integrable (ν₀ ν₁ : Measure X)
    (plan : Measure C(Time,X))
    (hopt : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1)))) (p : X)
    (h0 : Integrable (fun x => dist p x^2) ν₀)
    (h1 : Integrable (fun x => dist p x^2) ν₁) :
    Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) plan := by
  obtain ⟨he0,he1⟩ := optimalPlan_endpoints ν₀ ν₁ plan hopt
  rw [← he0] at h0
  rw [← he1] at h1
  apply ((h0.comp_measurable (measurable_path_eval 0)).const_mul 2 |>.add
    ((h1.comp_measurable (measurable_path_eval 1)).const_mul 2)).mono'
    (((continuous_eval_const 0).dist (continuous_eval_const 1)).pow 2).aestronglyMeasurable
  filter_upwards with γ
  simp only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_of_nonneg dist_nonneg,Pi.add_apply,Function.comp_apply]
  have hd := dist_triangle (γ 0) p (γ 1)
  rw [dist_comm (γ 0) p] at hd
  nlinarith [dist_nonneg (x := γ 0) (y := γ 1),sq_nonneg (dist p (γ 0)-dist p (γ 1))]

 theorem FullCD.exists_finite_entropy_exp_plan (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀.AbsolutelyContinuous μ) (h₁ : ν₁.AbsolutelyContinuous μ)
    (hm₀ : FiniteSecondMoment ν₀) (hm₁ : FiniteSecondMoment ν₁)
    (hEnt₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (hEnt₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal * Real.log (ν₁.rnDeriv μ x).toReal) μ)
    (p : X) {a : ℝ} (ha : 0 ≤ a)
    (hneg : Integrable (fun x => Real.exp (-a*dist p x)) μ)
    (hexp₀ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₀)
    (hexp₁ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₁)
    (hd₀ : Integrable (fun x => dist p x^2) ν₀)
    (hd₁ : Integrable (fun x => dist p x^2) ν₁) :
    ∃ plan : Measure C(Time,X), IsProbabilityMeasure plan ∧
      (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))) ∧
      ∀ t : Time, let ν := plan.map (fun γ => γ t)
        ν.AbsolutelyContinuous μ ∧
        Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ ∧
        (∫x, (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal ∂μ) ≤
          (1-(t:ℝ))*(∫x, (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal ∂μ) +
          (t:ℝ)*(∫x, (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal ∂μ) +
          ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan) := by
  obtain ⟨plan,hp,hg,hopt,hineq⟩ := hcd ν₀ ν₁ inferInstance inferInstance h₀ h₁ hm₀ hm₁
  let := hp
  have hd := optimalPlan_dist_sq_integrable ν₀ ν₁ plan hopt p hd₀ hd₁
  have hlog₀ := (integrable_toReal_rnDeriv_mul_iff h₀).mp hEnt₀
  have hlog₁ := (integrable_toReal_rnDeriv_mul_iff h₁).mp hEnt₁
  have hInt₀ : (∫x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀) =
      ∫x, (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal ∂μ := by
    simpa only [smul_eq_mul] using (integral_rnDeriv_smul (f := fun x =>
      Real.log (ν₀.rnDeriv μ x).toReal) h₀).symm
  have hInt₁ : (∫x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁) =
      ∫x, (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal ∂μ := by
    simpa only [smul_eq_mul] using (integral_rnDeriv_smul (f := fun x =>
      Real.log (ν₁.rnDeriv μ x).toReal) h₁).symm
  refine ⟨plan,hp,hg,hopt,fun t => ?_⟩
  let : IsProbabilityMeasure (plan.map (fun γ => γ t)) := inferInstance
  have hhalf := integrable_rnDeriv_half_of_exp_moment μ (plan.map (fun γ => γ t)) p a hneg
    (optimalPlan_exp_dist_integrable ν₀ ν₁ plan hopt hg p ha hexp₀ hexp₁ t)
  refine ⟨cd_plan_absolutelyContinuous_half μ K n ν₀ ν₁ h₀ h₁ plan hopt t
    (fun N hN => hineq N hN t) hhalf,?_⟩
  have hh := cd_plan_entropy_bound_half μ K n ν₀ ν₁ h₀ h₁ hlog₀ hlog₁ plan hopt hd t
    (fun N hN => hineq N hN t) hhalf
  simpa only [hInt₀,hInt₁] using hh
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
 theorem density_entropy_supporting_line {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    a*Real.log a-b*Real.log b ≤ (a-b)+(a-b)*Real.log a := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp only [zero_mul,sub_zero]
    linarith
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hb.le
  field_simp at hm
  nlinarith

 theorem integral_entropy_subgradient {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfpos : ∀ᵐ x ∂μ, 0 < f x) (hg0 : 0 ≤ᵐ[μ] g)
    (heF : Integrable (fun x => f x*Real.log (f x)) μ)
    (heG : Integrable (fun x => g x*Real.log (g x)) μ)
    (hglog : Integrable (fun x => g x*Real.log (f x)) μ)
    (hmass : (∫x, f x ∂μ) = ∫x, g x ∂μ) :
    (∫x, f x*Real.log (f x) ∂μ)-(∫x, g x*Real.log (g x) ∂μ) ≤
      (∫x, f x*Real.log (f x) ∂μ)-(∫x, g x*Real.log (f x) ∂μ) := by
  have hi := (hf.sub hg).add (heF.sub hglog)
  have h := integral_mono_ae (heF.sub heG) hi (by
    filter_upwards [hfpos,hg0] with x ha hb
    simpa only [Pi.add_apply,Pi.sub_apply,sub_mul] using density_entropy_supporting_line ha hb)
  simp only [Pi.add_apply,Pi.sub_apply] at h
  have hadd := integral_add (hf.sub hg) (heF.sub hglog)
  simp only [Pi.sub_apply] at hadd
  rw [integral_sub heF heG,hadd,
    integral_sub hf hg,integral_sub heF hglog,hmass,sub_self,zero_add] at h
  exact h

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
omit [MetricSpace X] [BorelSpace X] in
 theorem probability_entropy_subgradient (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν]
    (h0 : ν₀ ≪ μ) (hν : ν ≪ μ)
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hlog : Integrable (fun x => Real.log (ν₀.rnDeriv μ x).toReal) ν) :
    (∫x, (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal ∂μ)-
      (∫x, (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal ∂μ) ≤
      (∫x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀)-
      (∫x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν) := by
  have hi₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν₀ Set.univ))
  have hi : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν Set.univ))
  have hH := integral_entropy_subgradient μ _ _ hi₀ hi hpos
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) he0 he
    ((integrable_toReal_rnDeriv_mul_iff hν).mpr hlog) (by
      rw [Measure.integral_toReal_rnDeriv h0,Measure.integral_toReal_rnDeriv hν]
      simp)
  have hI0 := integral_rnDeriv_smul (f := fun x => Real.log (ν₀.rnDeriv μ x).toReal) h0
  have hI := integral_rnDeriv_smul (f := fun x => Real.log (ν₀.rnDeriv μ x).toReal) hν
  simp only [smul_eq_mul] at hI0 hI
  simpa only [hI0,hI] using hH
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X]
 theorem slopeAtScale_le_lipschitz {φ : X → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (r : ℝ) (x : X) : slopeAtScale φ r x ≤ C := by
  refine iSup_le fun y => iSup_le fun _ => iSup_le fun hne => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (dist_pos.mpr hne.symm)).mpr
  simpa only [Real.dist_eq,dist_comm x y] using hφ.dist_le_mul y x

 theorem geodesic_limsup_increment (φ : X → ℝ) {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (τ : ℕ → Time) (hτ : ∀ i, 0 < (τ i:ℝ))
    (hlim : Tendsto (fun i => (τ i:ℝ)) atTop (𝓝 0)) :
    limsup (fun i => ENNReal.ofReal (|φ (γ (τ i))-φ (γ 0)|/(τ i:ℝ))) atTop ≤
      localSlope φ (γ 0)*ENNReal.ofReal (dist (γ 0) (γ 1)) := by
  have hd (i : ℕ) : dist (γ 0) (γ (τ i)) = (τ i:ℝ)*dist (γ 0) (γ 1) := by
    have h := hγ 0 (τ i)
    change dist (γ 0) (γ (τ i)) = |0-(τ i:ℝ)| *dist (γ 0) (γ 1) at h
    simpa only [zero_sub,abs_neg,abs_of_nonneg (hτ i).le] using h
  by_cases hD : dist (γ 0) (γ 1) = 0
  · have he (i : ℕ) : γ (τ i) = γ 0 := by
      apply (dist_eq_zero.mp _).symm
      rw [hd,hD,mul_zero]
    simp [he,hD]
  have hD0 : ENNReal.ofReal (dist (γ 0) (γ 1)) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne dist_nonneg (Ne.symm hD))).ne'
  rw [mul_comm]
  simp only [localSlope,ENNReal.mul_iInf_of_ne hD0 ENNReal.ofReal_ne_top]
  refine le_iInf fun r => le_iInf fun hr => ?_
  have hsmall : ∀ᶠ i in atTop, dist (γ 0) (γ (τ i)) < r := by
    have hl := hlim.mul_const (dist (γ 0) (γ 1))
    simp only [zero_mul] at hl
    exact (hl.eventually (gt_mem_nhds hr)).mono fun i hi => by rwa [hd]
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hsmall] with i hi
  by_cases he : γ (τ i) = γ 0
  · simp only [he,sub_self,abs_zero,zero_div,ENNReal.ofReal_zero]
    exact bot_le
  · have hs := slopeAtScale_term_le φ hi he
    calc
      _ = ENNReal.ofReal ((|φ (γ (τ i))-φ (γ 0)|/dist (γ 0) (γ (τ i)))*dist (γ 0) (γ 1)) := by
        congr 1
        rw [hd]
        field_simp
      _ = ENNReal.ofReal (|φ (γ (τ i))-φ (γ 0)|/dist (γ 0) (γ (τ i)))*
          ENNReal.ofReal (dist (γ 0) (γ 1)) := ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by simpa only [mul_comm,slopeAtScale] using mul_le_mul' hs (le_refl (ENNReal.ofReal (dist (γ 0) (γ 1))))
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
omit [MeasurableSpace X] [BorelSpace X] in
 theorem limsup_geodesic_increment_integral_le (plan : Measure C(Time,X))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ) (φ : X → ℝ) {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) plan)
    (τ : ℕ → Time) (hτ : ∀ i, 0 < (τ i:ℝ))
    (hlim : Tendsto (fun i => (τ i:ℝ)) atTop (𝓝 0)) :
    limsup (fun i => ∫⁻γ : C(Time,X), ENNReal.ofReal
      (|φ (γ (τ i))-φ (γ 0)|/(τ i:ℝ)) ∂plan) atTop ≤
      ∫⁻γ : C(Time,X), localSlope φ (γ 0)*ENNReal.ofReal (dist (γ 0) (γ 1)) ∂plan := by
  have hmeas (i : ℕ) : Measurable (fun γ : C(Time,X) => ENNReal.ofReal
      (|φ (γ (τ i))-φ (γ 0)|/(τ i:ℝ))) :=
    ((((hφ.continuous.comp (continuous_eval_const (τ i))).sub
      (hφ.continuous.comp (continuous_eval_const 0))).abs).div_const _).measurable.ennreal_ofReal
  have hb (i : ℕ) : ∀ᵐ γ ∂plan, ENNReal.ofReal (|φ (γ (τ i))-φ (γ 0)|/(τ i:ℝ)) ≤
      ENNReal.ofReal ((C:ℝ)*dist (γ 0) (γ 1)) := by
    filter_upwards [hg] with γ hγ
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (hτ i)).mpr
    have h := hφ.dist_le_mul (γ (τ i)) (γ 0)
    rw [hγ] at h
    have ha : |(τ i:ℝ)-(0:Time)| = (τ i:ℝ) := by
      change |(τ i:ℝ)-0| = (τ i:ℝ)
      rw [sub_zero,abs_of_pos (hτ i)]
    simp only [Real.dist_eq,ha] at h
    nlinarith
  refine (limsup_lintegral_le _ hmeas hb (hD.const_mul (C:ℝ)).lintegral_lt_top.ne).trans ?_
  apply lintegral_mono_ae
  filter_upwards [hg] with γ hγ
  exact geodesic_limsup_increment φ hγ τ hτ hlim

omit [MeasurableSpace X] [BorelSpace X] in
 theorem geodesic_increment_integrable (plan : Measure C(Time,X))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ) (φ : X → ℝ) {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) plan)
    (t : Time) : Integrable (fun γ : C(Time,X) => φ (γ t)-φ (γ 0)) plan := by
  apply (hD.const_mul ((C:ℝ)*(t:ℝ))).mono'
    ((hφ.continuous.comp (continuous_eval_const t)).sub
      (hφ.continuous.comp (continuous_eval_const 0))).aestronglyMeasurable
  filter_upwards [hg] with γ hγ
  have h := hφ.dist_le_mul (γ t) (γ 0)
  rw [hγ] at h
  have ha : |(t:ℝ)-(0:Time)| = (t:ℝ) := by
    change |(t:ℝ)-0| = (t:ℝ)
    rw [sub_zero,abs_of_nonneg t.property.1]
  simpa only [Function.comp_apply,Pi.sub_apply,Real.norm_eq_abs,Real.dist_eq,ha,mul_assoc] using h
end

 
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def boltzmannEntropy (μ ν : Measure X) : ℝ :=
  ∫x, (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal ∂μ

omit [MetricSpace X] [BorelSpace X] in
 theorem entropy_subgradient_rep (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν]
    (h0 : ν₀ ≪ μ) (hν : ν ≪ μ)
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (φ : X → ℝ) (hrep : φ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (hi : Integrable φ ν) :
    boltzmannEntropy μ ν₀-boltzmannEntropy μ ν ≤ (∫x, φ x ∂ν₀)-(∫x, φ x ∂ν) := by
  have h := probability_entropy_subgradient μ ν₀ ν h0 hν hpos he0 he
    (hi.congr (hν.ae_eq hrep))
  simpa only [boltzmannEntropy,integral_congr_ae (h0.ae_eq hrep),
    integral_congr_ae (hν.ae_eq hrep)] using h

 theorem entropy_secant_le {E0 E1 Et K t d b : ℝ} (ht : 0 < t)
    (hc : Et ≤ (1-t)*E0+t*E1+((-K)*t*(1-t)/2)*d)
    (hs : E0-Et ≤ b) : E0-E1+(K*(1-t)/2)*d ≤ b/t := by
  apply (le_div_iff₀ ht).mpr
  nlinarith only [hc,hs]

 theorem entropy_plan_slope_bound (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h0 : ν₀ ≪ μ)
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (φ : X → ℝ) {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hrep : φ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hmap0 : plan.map (fun γ => γ 0) = ν₀)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) plan)
    (K : ℝ)
    (hc : ∀ t : Time, let ν := plan.map (fun γ => γ t)
      ν ≪ μ ∧
      Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ ν ≤ (1-(t:ℝ))*boltzmannEntropy μ ν₀+
        (t:ℝ)*boltzmannEntropy μ ν₁+
        ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan)) :
    ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+
      (K/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan)) ≤
      ∫⁻γ : C(Time,X), localSlope φ (γ 0)*ENNReal.ofReal (dist (γ 0) (γ 1)) ∂plan := by
  have hi0 : Integrable φ ν₀ :=
    ((integrable_toReal_rnDeriv_mul_iff h0).mp he0).congr (h0.ae_eq hrep).symm
  have hi0p : Integrable (fun γ : C(Time,X) => φ (γ 0)) plan := by
    rw [← hmap0] at hi0
    exact hi0.comp_measurable (measurable_path_eval 0)
  have hit (t : Time) : Integrable (fun γ : C(Time,X) => φ (γ t)) plan := by
    apply ((geodesic_increment_integrable plan hg φ hφ hD t).add hi0p).congr
    filter_upwards with γ
    exact sub_add_cancel _ _
  have hit' (t : Time) : Integrable φ (plan.map (fun γ => γ t)) :=
    (integrable_map_measure hφ.continuous.aestronglyMeasurable
      (measurable_path_eval t).aemeasurable).mpr (hit t)
  let τ : ℕ → Time := fun i => ⟨1/((i:ℝ)+1),by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])⟩
  have hτ (i : ℕ) : 0 < (τ i:ℝ) := by dsimp [τ]; positivity
  have hlim : Tendsto (fun i => (τ i:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let d : ℝ := ∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂plan
  let a : ℕ → ℝ := fun i => boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+
    (K*(1-(τ i:ℝ))/2)*d
  have ha (i : ℕ) : ENNReal.ofReal (a i) ≤
      ∫⁻γ : C(Time,X), ENNReal.ofReal (|φ (γ (τ i))-φ (γ 0)|/(τ i:ℝ)) ∂plan := by
    let ν := plan.map (fun γ => γ (τ i))
    let : IsProbabilityMeasure ν := inferInstance
    have hs := entropy_subgradient_rep μ ν₀ ν h0 (hc (τ i)).1 hpos he0
      (hc (τ i)).2.1 φ hrep (hit' (τ i))
    have hp : a i ≤ (∫γ, φ (γ 0)-φ (γ (τ i)) ∂plan)/(τ i:ℝ) := by
      have he := (hc (τ i)).2.2
      rw [integral_sub hi0p (hit (τ i))]
      have hI0 : (∫γ, φ (γ 0) ∂plan) = ∫x, φ x ∂ν₀ := by
        rw [← hmap0,integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.aestronglyMeasurable]
      have hIt : (∫γ, φ (γ (τ i)) ∂plan) = ∫x, φ x ∂ν := by
        exact (integral_map (measurable_path_eval (τ i)).aemeasurable hφ.continuous.aestronglyMeasurable).symm
      rw [hI0,hIt]
      exact entropy_secant_le (hτ i) he hs
    have hI := (hi0p.sub (hit (τ i))).div_const (τ i:ℝ)
    calc
      ENNReal.ofReal (a i) ≤ ENNReal.ofReal (∫γ, (φ (γ 0)-φ (γ (τ i)))/(τ i:ℝ) ∂plan) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div]
        exact hp
      _ ≤ ∫⁻γ, ENNReal.ofReal ((φ (γ 0)-φ (γ (τ i)))/(τ i:ℝ)) ∂plan :=
        ofReal_integral_le_lintegral_ofReal plan _ hI
      _ ≤ _ := by
        apply lintegral_mono
        intro γ
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (hτ i).le
        exact (le_abs_self _).trans_eq (abs_sub_comm _ _)
  have hla : Tendsto (fun i => ENNReal.ofReal (a i)) atTop
      (𝓝 (ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+(K/2)*d))) := by
    apply ENNReal.tendsto_ofReal
    dsimp [a]
    simpa only [sub_zero,mul_one] using
      (tendsto_const_nhds (x := boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁)).add
      ((((tendsto_const_nhds (x := K)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).sub hlim)).div_const 2).mul_const d)
  calc
    _ = limsup (fun i => ENNReal.ofReal (a i)) atTop := hla.limsup_eq.symm
    _ ≤ limsup (fun i => ∫⁻γ : C(Time,X), ENNReal.ofReal
        (|φ (γ (τ i))-φ (γ 0)|/(τ i:ℝ)) ∂plan) atTop :=
      limsup_le_limsup (Eventually.of_forall ha)
    _ ≤ _ := limsup_geodesic_increment_integral_le plan hg φ hφ hD τ hτ hlim

end RegularPointCoordinates

end OAI
