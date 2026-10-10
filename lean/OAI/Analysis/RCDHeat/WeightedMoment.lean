import Mathlib
import OAI.Analysis.RCDHeat.HeatMoments
import OAI.Analysis.RCDHeat.SignedEntropySupport
import OAI.Analysis.RCDHeat.WeightedRenyi

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedMoment, WeightedCD. -/



namespace RegularPointCoordinates

section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
 theorem rpow_half_weight_bound {z : ℝ} (hz : 0 ≤ z) (V : ℝ) :
    z^(1/2:ℝ) ≤ Real.exp V*z+Real.exp (-V) := by
  have hs : (z^(1/2:ℝ))^2 = z := by rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hz]
  have hn := Real.rpow_nonneg hz (1/2:ℝ)
  have he := Real.exp_pos V
  have he' := Real.exp_pos (-V)
  have heq : Real.exp V*Real.exp (-V) = 1 := by rw [← Real.exp_add]; simp
  by_cases h : z^(1/2:ℝ) ≤ Real.exp (-V)
  · exact h.trans (le_add_of_nonneg_left (mul_nonneg he.le hz))
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) he.le
    rw [heq] at hh
    have hh' := mul_le_mul_of_nonneg_right hh hn
    nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
 theorem heatAt_exp_dist_integrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (a*dist p x)*heatAt μ hQ t f x) μ := by
  have hI := (heatAt_exponential_square_integrable μ hQ f p hf
    (show 0 ≤ B+1+2*a by linarith) ht).add
    (integrable_exp_neg_dist_of_volume μ p hA hB (by linarith : B < B+1) hvol)
  apply hI.mono' ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.dist continuous_id))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _))
  filter_upwards with x
  have hh := exponential_moment_young (B+1) (dist p x)
    (Real.exp (a*dist p x)*heatAt μ hQ t f x) 0
  simp only [Nat.mul_zero,pow_zero,one_mul,mul_pow,← Real.exp_nat_mul,← mul_assoc,← Real.exp_add] at hh
  simp only [Pi.add_apply]
  convert hh using 1 <;> first | rfl | (congr 2; ring_nf)

 theorem heatMeasure_exp_dist_integrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (a*dist p x)) (heatMeasure μ hQ t f) := by
  rw [heatMeasure,integrable_withDensity_iff_integrable_smul₀'
    (Lp.aestronglyMeasurable (heatAt μ hQ t f)).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply (heatAt_exp_dist_integrable μ hQ p hA hB hvol f hf ha ht).congr
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul,mul_comm]

omit [ProperSpace X] [BorelSpace X] [μ.Regular] hQ in
 theorem integrable_rnDeriv_half_of_exp_moment [SigmaFinite μ]
    (ν : Measure X) [IsFiniteMeasure ν] (p : X) (a : ℝ)
    (hneg : Integrable (fun x => Real.exp (-a*dist p x)) μ)
    (hpos : Integrable (fun x => Real.exp (a*dist p x)) ν) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal^(1/2:ℝ)) μ := by
  have hi := (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv ν μ)
    (Measure.rnDeriv_lt_top ν μ)).mp (hpos.mono_measure (Measure.withDensity_rnDeriv_le ν μ))
  have hi' : Integrable (fun x => Real.exp (a*dist p x)*(ν.rnDeriv μ x).toReal) μ := by
    simpa only [smul_eq_mul,mul_comm] using hi
  apply (hi'.add hneg).mono' ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.pow_const _).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  simpa only [neg_mul, Pi.add_apply] using rpow_half_weight_bound (ENNReal.toReal_nonneg (a := ν.rnDeriv μ x)) (a*dist p x)

attribute [local instance] pathBorel pathBorelSpace
omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] μ hQ in
 theorem geodesic_exp_dist_bound (p : X) {a : ℝ} (ha : 0 ≤ a) {γ : C(Time,X)}
    (hγ : IsGeodesic γ) (t : Time) :
    Real.exp (a*dist p (γ t)) ≤ Real.exp ((3*a)*dist p (γ 0))+Real.exp ((3*a)*dist p (γ 1)) := by
  have hb : dist p (γ t) ≤ 2*dist p (γ 0)+dist p (γ 1) := by
    have h0 := hγ 0 t
    have ht : |(0:Time).val-(t:ℝ)| = (t:ℝ) := by
      change |0-(t:ℝ)| = (t:ℝ)
      simp only [zero_sub,abs_neg,abs_of_nonneg t.property.1]
    rw [ht] at h0
    calc
      _ ≤ dist p (γ 0)+dist (γ 0) (γ t) := dist_triangle _ _ _
      _ ≤ dist p (γ 0)+dist (γ 0) (γ 1) := by rw [h0]; nlinarith [dist_nonneg (x := γ 0) (y := γ 1),t.property.2]
      _ ≤ _ := by have := dist_triangle (γ 0) p (γ 1); rw [dist_comm (γ 0) p] at this; linarith
  by_cases h : dist p (γ 0) ≤ dist p (γ 1)
  · have hh : a*dist p (γ t) ≤ (3*a)*dist p (γ 1) := by nlinarith
    exact (Real.exp_le_exp.mpr hh).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  · have hh : a*dist p (γ t) ≤ (3*a)*dist p (γ 0) := by nlinarith [le_of_not_ge h]
    exact (Real.exp_le_exp.mpr hh).trans (le_add_of_nonneg_right (Real.exp_pos _).le)

omit [ProperSpace X] μ hQ in
 theorem optimalPlan_exp_dist_integrable (ν₀ ν₁ : Measure X)
    (plan : Measure C(Time,X)) (hopt : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ) (p : X) {a : ℝ} (ha : 0 ≤ a)
    (h0 : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₀)
    (h1 : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₁) (t : Time) :
    Integrable (fun x => Real.exp (a*dist p x)) (plan.map (fun γ => γ t)) := by
  obtain ⟨he0,he1⟩ := optimalPlan_endpoints ν₀ ν₁ plan hopt
  rw [← he0] at h0
  rw [← he1] at h1
  have hi0 := h0.comp_measurable (measurable_path_eval 0)
  have hi1 := h1.comp_measurable (measurable_path_eval 1)
  have hm : Measurable (fun x : X => Real.exp (a*dist p x)) := by fun_prop
  apply (integrable_map_measure hm.aestronglyMeasurable (measurable_path_eval t).aemeasurable).mpr
  apply (hi0.add hi1).mono' ((hm.comp (measurable_path_eval t)).aestronglyMeasurable)
  filter_upwards [hg] with γ hγ
  simp only [Function.comp_apply,Pi.add_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact geodesic_exp_dist_bound p ha hγ t
end

 
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
 theorem lintegral_rpow_tendsto_mass_half {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ≥0∞) (hρ : Measurable ρ)
    (hρfin : ∫⁻x, ρ x ∂μ ≠ ∞) (hhalf : ∫⁻x, ρ x^(1/2:ℝ) ∂μ ≠ ∞)
    (q : ℕ → ℝ) (hq : ∀ i, 1/2 ≤ q i) (hqle : ∀ i, q i ≤ 1)
    (hqlim : Tendsto q atTop (𝓝 1)) :
    Tendsto (fun i => ∫⁻x, ρ x^(q i) ∂μ) atTop (𝓝 (∫⁻x, ρ x ∂μ)) := by
  apply tendsto_lintegral_of_dominated_convergence (fun x => ρ x^(1/2:ℝ)+ρ x)
    (fun i => hρ.pow_const _)
  · intro i
    filter_upwards with x
    by_cases hx : ρ x ≤ 1
    · exact (ENNReal.rpow_le_rpow_of_exponent_ge hx (hq i)).trans le_self_add
    · have hh := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) (hqle i)
      rw [ENNReal.rpow_one] at hh
      exact hh.trans le_add_self
  · rw [lintegral_add_left (hρ.pow_const _)]
    exact ENNReal.add_ne_top.mpr ⟨hhalf,hρfin⟩
  · filter_upwards [ae_lt_top hρ hρfin] with x hx
    exact ennreal_rpow_tendsto_one hx.ne q (fun i => by linarith [hq i]) hqlim

 theorem rnDeriv_power_lintegral_eq_of_integrable {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν] {q : ℝ} (hq : 0 ≤ q)
    (hi : Integrable (fun x => (ν.rnDeriv μ x).toReal^q) μ) :
    (∫⁻x, (ν.rnDeriv μ x)^q ∂μ) = ENNReal.ofReal (∫x, (ν.rnDeriv μ x).toReal^q ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq,ENNReal.ofReal_toReal hx.ne]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
theorem cd_plan_absolutelyContinuous_half
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀.AbsolutelyContinuous μ) (h₁ : ν₁.AbsolutelyContinuous μ)
    (plan : Measure C(Time, X)) [IsProbabilityMeasure plan]
    (hopt : IsOptimalCoupling ν₀ ν₁ (Measure.map (fun γ => (γ 0, γ 1)) plan))
    (t : Time)
    (hcd : ∀ N : ℝ, (n:ℝ) ≤ N →
      (∫⁻ γ, tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) *
        (ν₀.rnDeriv μ (γ 0))^(-(1/N)) +
        tau K N (t:ℝ) (dist (γ 0) (γ 1)) *
        (ν₁.rnDeriv μ (γ 1))^(-(1/N)) ∂plan) ≤
        renyiIntegral μ (Measure.map (fun γ => γ t) plan) N)
    (hhalf : Integrable (fun x => ((Measure.map (fun γ => γ t) plan).rnDeriv μ x).toReal^(1/2:ℝ)) μ) :
    (Measure.map (fun γ => γ t) plan).AbsolutelyContinuous μ := by
  let ν := Measure.map (fun γ => γ t) plan
  let : IsProbabilityMeasure ν := inferInstance
  obtain ⟨he₀, he₁⟩ := optimalPlan_endpoints ν₀ ν₁ plan hopt
  have hrn₀ : ∀ᵐ γ ∂plan, ν₀.rnDeriv μ (γ 0) ≠ 0 ∧ ν₀.rnDeriv μ (γ 0) ≠ ∞ := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
      (p := fun x => ν₀.rnDeriv μ x ≠ 0 ∧ ν₀.rnDeriv μ x ≠ ∞)
    rw [he₀]
    filter_upwards [Measure.rnDeriv_pos h₀, h₀.ae_le (Measure.rnDeriv_lt_top ν₀ μ)] with x hpx hfx
    exact ⟨hpx.ne', hfx.ne⟩
  have hrn₁ : ∀ᵐ γ ∂plan, ν₁.rnDeriv μ (γ 1) ≠ 0 ∧ ν₁.rnDeriv μ (γ 1) ≠ ∞ := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
      (p := fun x => ν₁.rnDeriv μ x ≠ 0 ∧ ν₁.rnDeriv μ x ≠ ∞)
    rw [he₁]
    filter_upwards [Measure.rnDeriv_pos h₁, h₁.ae_le (Measure.rnDeriv_lt_top ν₁ μ)] with x hpx hfx
    exact ⟨hpx.ne', hfx.ne⟩
  let F : ℕ → C(Time, X) → ℝ≥0∞ := fun i γ =>
    ENNReal.ofReal ((1-(t:ℝ))*Real.exp
      (-|K| *(dist (γ 0) (γ 1))^2*(1-(1-(t:ℝ))^2)/(6*((n:ℝ)+i+2)))) *
      (ν₀.rnDeriv μ (γ 0))^(-(1/((n:ℝ)+i+2))) +
    ENNReal.ofReal ((t:ℝ)*Real.exp
      (-|K| *(dist (γ 0) (γ 1))^2*(1-(t:ℝ)^2)/(6*((n:ℝ)+i+2)))) *
      (ν₁.rnDeriv μ (γ 1))^(-(1/((n:ℝ)+i+2)))
  have hFm : ∀ i, Measurable (F i) := by
    intro i
    have hm₀ := measurable_path_eval (X := X) 0
    have hm₁ := measurable_path_eval (X := X) 1
    have hr₀ := (Measure.measurable_rnDeriv ν₀ μ).comp hm₀
    have hr₁ := (Measure.measurable_rnDeriv ν₁ μ).comp hm₁
    have hd : Continuous (fun γ : C(Time, X) => dist (γ 0) (γ 1)) :=
      (continuous_eval_const 0).dist (continuous_eval_const 1)
    have hA : Continuous (fun γ : C(Time, X) => ENNReal.ofReal ((1-(t:ℝ))*Real.exp
      (-|K| *(dist (γ 0) (γ 1))^2*(1-(1-(t:ℝ))^2)/(6*((n:ℝ)+i+2))))) := by
      apply ENNReal.continuous_ofReal.comp
      fun_prop
    have hB : Continuous (fun γ : C(Time, X) => ENNReal.ofReal ((t:ℝ)*Real.exp
      (-|K| *(dist (γ 0) (γ 1))^2*(1-(t:ℝ)^2)/(6*((n:ℝ)+i+2))))) := by
      apply ENNReal.continuous_ofReal.comp
      fun_prop
    exact (hA.measurable.mul (hr₀.pow_const _)).add (hB.measurable.mul (hr₁.pow_const _))
  have hFlim : ∀ᵐ γ ∂plan, Tendsto (fun i => F i γ) atTop (𝓝 1) := by
    filter_upwards [hrn₀, hrn₁] with γ hγ₀ hγ₁
    have hA := gaussian_density_tendsto n K (1-(t:ℝ)) (dist (γ 0) (γ 1)) _ hγ₀.1 hγ₀.2
    have hB := gaussian_density_tendsto n K (t:ℝ) (dist (γ 0) (γ 1)) _ hγ₁.1 hγ₁.2
    have heq : ENNReal.ofReal (1-(t:ℝ)) + ENNReal.ofReal (t:ℝ) = 1 := by
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr t.property.2) t.property.1]
      simp
    simpa only [F, heq] using hA.add hB
  have hlim : Tendsto (fun i : ℕ => renyiIntegral μ ν ((n:ℝ)+i+2)) atTop
      (𝓝 (∫⁻ x, ν.rnDeriv μ x ∂μ)) := by
    apply lintegral_rpow_tendsto_mass_half μ (ν.rnDeriv μ) (Measure.measurable_rnDeriv ν μ)
      (ne_top_of_le_ne_top (measure_ne_top _ _) Measure.lintegral_rnDeriv_le)
      (by rw [rnDeriv_power_lintegral_eq_of_integrable μ ν (by norm_num : (0:ℝ) ≤ 1/2) hhalf]; exact ENNReal.ofReal_ne_top)
    · intro i
      have hN : 2 ≤ (n:ℝ)+i+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) i]
      have hrec : 1/((n:ℝ)+i+2) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hN
      linarith
    · intro i
      have : 0 ≤ 1/((n:ℝ)+i+2) := by positivity
      linarith
    · simpa using tendsto_const_nhds.sub (dimension_reciprocal_tendsto n)
  have hmono : ∀ i : ℕ, (∫⁻ γ, F i γ ∂plan) ≤ renyiIntegral μ ν ((n:ℝ)+i+2) := by
    intro i
    refine le_trans (lintegral_mono fun γ => ?_)
      (hcd ((n:ℝ)+i+2) (by linarith [Nat.cast_nonneg (α := ℝ) i]))
    apply add_le_add
    · exact mul_le_mul_left
        (tau_gaussian_lower K ((n:ℝ)+i+2) (dist (γ 0) (γ 1)) (1-(t:ℝ))
          (by nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) i]) dist_nonneg (sub_nonneg.mpr t.property.2) (by linarith [t.property.1])) _
    · exact mul_le_mul_left
        (tau_gaussian_lower K ((n:ℝ)+i+2) (dist (γ 0) (γ 1)) (t:ℝ)
          (by nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) i]) dist_nonneg t.property.1 t.property.2) _
  have hmass : 1 ≤ ∫⁻ x, ν.rnDeriv μ x ∂μ := by
    calc
      1 = ∫⁻ γ, liminf (fun i => F i γ) atTop ∂plan := by
        rw [lintegral_congr_ae (hFlim.mono fun _ h => h.liminf_eq)]
        simp
      _ ≤ liminf (fun i => ∫⁻ γ, F i γ ∂plan) atTop := lintegral_liminf_le hFm
      _ ≤ liminf (fun i : ℕ => renyiIntegral μ ν ((n:ℝ)+i+2)) atTop :=
        liminf_le_liminf (Eventually.of_forall hmono)
      _ = ∫⁻ x, ν.rnDeriv μ x ∂μ := hlim.liminf_eq
  exact absolutelyContinuous_of_rnDeriv_mass_one μ ν
    (le_antisymm (Measure.lintegral_rnDeriv_le.trans (by simp)) hmass)

theorem cd_plan_renyi_variation_bound_half
    (μ : Measure X) [SigmaFinite μ] (K N : ℝ) (hN : 2 ≤ N)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀.AbsolutelyContinuous μ) (h₁ : ν₁.AbsolutelyContinuous μ)
    (hlog₀ : Integrable (fun x => Real.log (ν₀.rnDeriv μ x).toReal) ν₀)
    (hlog₁ : Integrable (fun x => Real.log (ν₁.rnDeriv μ x).toReal) ν₁)
    (plan : Measure C(Time, X)) [IsProbabilityMeasure plan]
    (hopt : IsOptimalCoupling ν₀ ν₁ (Measure.map (fun γ => (γ 0, γ 1)) plan))
    (hd : Integrable (fun γ : C(Time, X) => (dist (γ 0) (γ 1))^2) plan)
    (t : Time)
    (hcd : (∫⁻ γ, tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) *
        (ν₀.rnDeriv μ (γ 0))^(-(1/N)) +
        tau K N (t:ℝ) (dist (γ 0) (γ 1)) *
        (ν₁.rnDeriv μ (γ 1))^(-(1/N)) ∂plan) ≤
        renyiIntegral μ (Measure.map (fun γ => γ t) plan) N)
    (hhalf : Integrable (fun x => ((Measure.map (fun γ => γ t) plan).rnDeriv μ x).toReal^(1/2:ℝ)) μ) :
    (1 - (∫ x, ((Measure.map (fun γ => γ t) plan).rnDeriv μ x).toReal^(1-1/N) ∂μ)) /
        (1/N) ≤
      (1-(t:ℝ))*(∫ x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀) +
      (t:ℝ)*(∫ x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁) +
      ((-K) *(t:ℝ)*(1-(t:ℝ))/2)*(∫ γ, (dist (γ 0) (γ 1))^2 ∂plan) := by
  have hN2 := hN
  have hN : 1 < N := lt_of_lt_of_le (by norm_num) hN2
  obtain ⟨he₀, he₁⟩ := optimalPlan_endpoints ν₀ ν₁ plan hopt
  have hL₀ : Integrable (fun γ : C(Time, X) => Real.log (ν₀.rnDeriv μ (γ 0)).toReal) plan := by
    have h : Integrable (fun x => Real.log (ν₀.rnDeriv μ x).toReal)
        (Measure.map (fun γ : C(Time, X) => γ 0) plan) := by rwa [he₀]
    exact h.comp_measurable (measurable_path_eval 0)
  have hL₁ : Integrable (fun γ : C(Time, X) => Real.log (ν₁.rnDeriv μ (γ 1)).toReal) plan := by
    have h : Integrable (fun x => Real.log (ν₁.rnDeriv μ x).toReal)
        (Measure.map (fun γ : C(Time, X) => γ 1) plan) := by rwa [he₁]
    exact h.comp_measurable (measurable_path_eval 1)
  let A : C(Time, X) → ℝ := fun γ =>
    (1-(t:ℝ))*Real.log (ν₀.rnDeriv μ (γ 0)).toReal +
    (t:ℝ)*Real.log (ν₁.rnDeriv μ (γ 1)).toReal +
    ((-K) *(t:ℝ)*(1-(t:ℝ))/2)*(dist (γ 0) (γ 1))^2
  have hAI : Integrable A plan := ((hL₀.const_mul _).add (hL₁.const_mul _)).add (hd.const_mul _)
  have hrn₀ : ∀ᵐ γ ∂plan, ν₀.rnDeriv μ (γ 0) ≠ 0 ∧ ν₀.rnDeriv μ (γ 0) ≠ ∞ := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
      (p := fun x => ν₀.rnDeriv μ x ≠ 0 ∧ ν₀.rnDeriv μ x ≠ ∞)
    rw [he₀]
    filter_upwards [Measure.rnDeriv_pos h₀, h₀.ae_le (Measure.rnDeriv_lt_top ν₀ μ)] with x hx hx'
    exact ⟨hx.ne', hx'.ne⟩
  have hrn₁ : ∀ᵐ γ ∂plan, ν₁.rnDeriv μ (γ 1) ≠ 0 ∧ ν₁.rnDeriv μ (γ 1) ≠ ∞ := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
      (p := fun x => ν₁.rnDeriv μ x ≠ 0 ∧ ν₁.rnDeriv μ x ≠ ∞)
    rw [he₁]
    filter_upwards [Measure.rnDeriv_pos h₁, h₁.ae_le (Measure.rnDeriv_lt_top ν₁ μ)] with x hx hx'
    exact ⟨hx.ne', hx'.ne⟩
  have hpoint : ∀ᵐ γ ∂plan, ENNReal.ofReal (1-A γ/N) ≤
      tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) * (ν₀.rnDeriv μ (γ 0))^(-(1/N)) +
      tau K N (t:ℝ) (dist (γ 0) (γ 1)) * (ν₁.rnDeriv μ (γ 1))^(-(1/N)) := by
    filter_upwards [hrn₀, hrn₁] with γ hγ₀ hγ₁
    have ha := tau_density_entropy_lower K N (dist (γ 0) (γ 1)) (1-(t:ℝ)) hN
      dist_nonneg (sub_nonneg.mpr t.property.2) (by linarith [t.property.1]) _ hγ₀.1 hγ₀.2
    have hb := tau_density_entropy_lower K N (dist (γ 0) (γ 1)) (t:ℝ) hN
      dist_nonneg t.property.1 t.property.2 _ hγ₁.1 hγ₁.2
    apply le_trans _ (add_le_add ha hb)
    convert ENNReal.ofReal_add_le
      (p := 1-(t:ℝ) - (1-(t:ℝ))/N*Real.log (ν₀.rnDeriv μ (γ 0)).toReal -
        (1-(t:ℝ))/N*((-K)*(dist (γ 0) (γ 1))^2*(1-(1-(t:ℝ))^2)/6))
      (q := (t:ℝ) - (t:ℝ)/N*Real.log (ν₁.rnDeriv μ (γ 1)).toReal -
        (t:ℝ)/N*((-K)*(dist (γ 0) (γ 1))^2*(1-(t:ℝ)^2)/6)) using 1
    congr 1
    dsimp [A]
    ring
  let ν := Measure.map (fun γ => γ t) plan
  let : IsProbabilityMeasure ν := inferInstance
  have hq0 : 0 < 1-1/N := by
    have h : 1/N < 1 := (div_lt_one (lt_trans zero_lt_one hN)).mpr hN
    linarith
  have hq1 : 1-1/N ≤ 1 := by have := one_div_pos.mpr (lt_trans zero_lt_one hN); linarith
  have hreal : 1-(∫ γ, A γ ∂plan)/N ≤ (∫ x, (ν.rnDeriv μ x).toReal^(1-1/N) ∂μ) := by
    have hineq := (ofReal_integral_le_lintegral_ofReal plan (fun γ => 1-A γ/N)
      ((integrable_const 1).sub (hAI.div_const N))).trans ((lintegral_mono_ae hpoint).trans hcd)
    change _ ≤ ∫⁻ x, (ν.rnDeriv μ x)^(1-1/N) ∂μ at hineq
    have hρI : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := by
      simpa only [IntegrableOn, Measure.restrict_univ] using
        (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν Set.univ))
    have hpI := integrable_density_power_of_sqrt μ (fun x => (ν.rnDeriv μ x).toReal)
      (Measure.measurable_rnDeriv ν μ).ennreal_toReal hρI
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hhalf
      (show 1/2 ≤ 1-1/N by have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hN2; linarith) hq1
    rw [rnDeriv_power_lintegral_eq_of_integrable μ ν hq0.le hpI] at hineq
    have hnonneg : 0 ≤ (∫ x, (ν.rnDeriv μ x).toReal^(1-1/N) ∂μ) :=
      integral_nonneg fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hineq' := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hineq
    simpa [integral_sub (integrable_const 1) (hAI.div_const N), integral_div] using hineq'
  have hInt₀ : (∫ γ, Real.log (ν₀.rnDeriv μ (γ 0)).toReal ∂plan) =
      ∫ x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀ := by
    have h := integral_map (μ := plan) (measurable_path_eval (X := X) 0).aemeasurable
      ((Real.measurable_log.comp (Measure.measurable_rnDeriv ν₀ μ).ennreal_toReal).aestronglyMeasurable)
    simpa only [Function.comp_def, he₀] using h.symm
  have hInt₁ : (∫ γ, Real.log (ν₁.rnDeriv μ (γ 1)).toReal ∂plan) =
      ∫ x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁ := by
    have h := integral_map (μ := plan) (measurable_path_eval (X := X) 1).aemeasurable
      ((Real.measurable_log.comp (Measure.measurable_rnDeriv ν₁ μ).ennreal_toReal).aestronglyMeasurable)
    simpa only [Function.comp_def, he₁] using h.symm
  have hAeq : (∫ γ, A γ ∂plan) =
      (1-(t:ℝ))*(∫ x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀) +
      (t:ℝ)*(∫ x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁) +
      ((-K) *(t:ℝ)*(1-(t:ℝ))/2)*(∫ γ, (dist (γ 0) (γ 1))^2 ∂plan) := by
    dsimp [A]
    have h012 := integral_add ((hL₀.const_mul (1-(t:ℝ))).add (hL₁.const_mul (t:ℝ)))
      (hd.const_mul ((-K) *(t:ℝ)*(1-(t:ℝ))/2))
    simp only [Pi.add_apply] at h012
    rw [h012, integral_add (hL₀.const_mul (1-(t:ℝ))) (hL₁.const_mul (t:ℝ)),
      integral_const_mul, integral_const_mul, integral_const_mul, hInt₀, hInt₁]
  rw [← hAeq]
  apply (div_le_iff₀ (one_div_pos.mpr (lt_trans zero_lt_one hN))).mpr
  dsimp only [ν] at hreal
  rw [mul_one_div]
  linarith [hreal]

theorem cd_plan_entropy_bound_half
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀.AbsolutelyContinuous μ) (h₁ : ν₁.AbsolutelyContinuous μ)
    (hlog₀ : Integrable (fun x => Real.log (ν₀.rnDeriv μ x).toReal) ν₀)
    (hlog₁ : Integrable (fun x => Real.log (ν₁.rnDeriv μ x).toReal) ν₁)
    (plan : Measure C(Time, X)) [IsProbabilityMeasure plan]
    (hopt : IsOptimalCoupling ν₀ ν₁ (Measure.map (fun γ => (γ 0, γ 1)) plan))
    (hd : Integrable (fun γ : C(Time, X) => (dist (γ 0) (γ 1))^2) plan)
    (t : Time)
    (hcd : ∀ N : ℝ, (n:ℝ) ≤ N →
      (∫⁻ γ, tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) *
        (ν₀.rnDeriv μ (γ 0))^(-(1/N)) +
        tau K N (t:ℝ) (dist (γ 0) (γ 1)) *
        (ν₁.rnDeriv μ (γ 1))^(-(1/N)) ∂plan) ≤
        renyiIntegral μ (Measure.map (fun γ => γ t) plan) N)
    (hhalf : Integrable (fun x => ((Measure.map (fun γ => γ t) plan).rnDeriv μ x).toReal^(1/2:ℝ)) μ) :
    let ν := Measure.map (fun γ => γ t) plan
    Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ ∧
      (∫ x, (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal ∂μ) ≤
      (1-(t:ℝ))*(∫ x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀) +
      (t:ℝ)*(∫ x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁) +
      ((-K) *(t:ℝ)*(1-(t:ℝ))/2)*(∫ γ, (dist (γ 0) (γ 1))^2 ∂plan) := by
  let ν := Measure.map (fun γ => γ t) plan
  let : IsProbabilityMeasure ν := inferInstance
  have hν : ν.AbsolutelyContinuous μ :=
    cd_plan_absolutelyContinuous_half μ K n ν₀ ν₁ h₀ h₁ plan hopt t hcd hhalf
  have hρI : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν Set.univ))
  have hmass : (∫ x, (ν.rnDeriv μ x).toReal ∂μ) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hν
  let q : ℕ → ℝ := fun i => 1-1/((n:ℝ)+i+4)
  have hdim (i : ℕ) : 4 ≤ (n:ℝ)+i+4 := by
    linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) i]
  have hdim' (i : ℕ) : (n:ℝ) ≤ (n:ℝ)+i+4 := by
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hq (i : ℕ) : 3/4 ≤ q i := by
    have hh : 1/((n:ℝ)+i+4) ≤ 1/4 :=
      one_div_le_one_div_of_le (by norm_num) (hdim i)
    dsimp [q]
    linarith
  have hq1 (i : ℕ) : q i < 1 := by
    dsimp [q]
    have := one_div_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (hdim i))
    linarith
  have hqlim : Tendsto q atTop (𝓝 1) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,show ∀ i : ℕ, (n:ℝ) + 2 + (i:ℝ) + 2 = (n:ℝ) + (i:ℝ) + 4 by intro i; ring,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub (dimension_reciprocal_tendsto (n+2))
  apply entropy_le_of_renyi_variation_bound_sqrt μ (fun x => (ν.rnDeriv μ x).toReal)
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal hρI
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hhalf q hq hq1 hqlim
    (fun _ => (1-(t:ℝ))*(∫ x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀) +
      (t:ℝ)*(∫ x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁) +
      ((-K) *(t:ℝ)*(1-(t:ℝ))/2)*(∫ γ, (dist (γ 0) (γ 1))^2 ∂plan)) _ tendsto_const_nhds
  intro i
  rw [hmass]
  have hh := cd_plan_renyi_variation_bound_half μ K ((n:ℝ)+i+4)
    (by linarith [hdim i] : 2 ≤ (n:ℝ)+i+4) ν₀ ν₁ h₀ h₁ hlog₀ hlog₁
    plan hopt hd t (hcd _ (hdim' i)) hhalf
  dsimp only [q]
  simpa only [sub_sub_cancel] using hh


end RegularPointCoordinates

end OAI
