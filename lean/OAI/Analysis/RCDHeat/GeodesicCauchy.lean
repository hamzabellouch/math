import Mathlib
import OAI.Analysis.RCDHeat.FisherLimit
import OAI.Analysis.RCDHeat.WeightedPlan

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: GeodesicCauchy, FullCDHWI, FullCDDescent, LogDensitySlope, SqrtDensityDescent, SquareDensityLaws, NormalizedTail. -/



namespace RegularPointCoordinates

section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem geodesic_slope_integral_cauchy (ν₀ : Measure X) (plan : Measure C(Time,X))
    (hmap0 : plan.map (fun γ => γ 0) = ν₀)
    (φ : X → ℝ) (hφ : Continuous φ)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) plan) :
    (∫⁻γ : C(Time,X), localSlope φ (γ 0)*ENNReal.ofReal (dist (γ 0) (γ 1)) ∂plan) ≤
      (∫⁻x, localSlope φ x^2 ∂ν₀)^(1/(2:ℝ))*
      (ENNReal.ofReal (∫γ, dist (γ 0) (γ 1)^2 ∂plan))^(1/(2:ℝ)) := by
  have hs := ENNReal.lintegral_mul_le_Lp_mul_Lq plan
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    ((localSlope_measurable hφ).comp (measurable_path_eval 0)).aemeasurable
    (((continuous_eval_const 0).dist (continuous_eval_const 1)).measurable.ennreal_ofReal).aemeasurable
  simp only [Pi.mul_apply,Function.comp_apply,ENNReal.rpow_two] at hs
  have hI0 : (∫⁻γ : C(Time,X), localSlope φ (γ 0)^2 ∂plan) = ∫⁻x, localSlope φ x^2 ∂ν₀ := by
    rw [← hmap0,lintegral_map ((localSlope_measurable hφ).pow_const 2) (measurable_path_eval 0)]
  have hId : (∫⁻γ : C(Time,X), ENNReal.ofReal (dist (γ 0) (γ 1))^2 ∂plan) =
      ENNReal.ofReal (∫γ, dist (γ 0) (γ 1)^2 ∂plan) := by
    rw [ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall fun γ => sq_nonneg _)]
    congr 1
    ext γ
    exact (ENNReal.ofReal_pow dist_nonneg 2).symm
  rwa [hI0,hId] at hs

omit [MeasurableSpace X] [BorelSpace X] in
 theorem geodesic_dist_integrable_of_sq (plan : Measure C(Time,X)) [IsFiniteMeasure plan]
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) plan) :
    Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) plan :=
  ((memLp_two_iff_integrable_sq
    ((continuous_eval_const 0).dist (continuous_eval_const 1)).aestronglyMeasurable).mpr hD).integrable
    (by norm_num)
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
 

 theorem FullCD.exists_HWI_exp_plan (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀ ≪ μ) (h₁ : ν₁ ≪ μ)
    (hm₀ : FiniteSecondMoment ν₀) (hm₁ : FiniteSecondMoment ν₁)
    (hEnt₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (hEnt₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal) μ)
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
      ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+
        (K/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan)) ≤
        (∫⁻x, localSlope φ x^2 ∂ν₀)^(1/(2:ℝ))*
        (ENNReal.ofReal (∫γ, dist (γ 0) (γ 1)^2 ∂plan))^(1/(2:ℝ)) := by
  obtain ⟨plan,hp,hg,ho,hc⟩ := FullCD.exists_finite_entropy_exp_plan μ K n hcd ν₀ ν₁ h₀ h₁
    hm₀ hm₁ hEnt₀ hEnt₁ p ha hneg hexp₀ hexp₁ hd₀ hd₁
  let := hp
  have hD := optimalPlan_dist_sq_integrable ν₀ ν₁ plan ho p hd₀ hd₁
  have hmap0 := (optimalPlan_endpoints ν₀ ν₁ plan ho).1
  refine ⟨plan,hp,hg,ho,?_⟩
  exact (entropy_plan_slope_bound μ ν₀ ν₁ h₀ hpos hEnt₀ φ hφ hrep plan hg hmap0
    (geodesic_dist_integrable_of_sq plan hD) K (by simpa only [boltzmannEntropy] using hc)).trans
      (geodesic_slope_integral_cauchy ν₀ plan hmap0 φ hφ.continuous hD)
end

 
section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace
 

 theorem FullCD.entropy_descent_le_coupling (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h₀ : ν₀ ≪ μ) (h₁ : ν₁ ≪ μ)
    (hm₀ : FiniteSecondMoment ν₀) (hm₁ : FiniteSecondMoment ν₁)
    (hEnt₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (hEnt₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal) μ)
    (p : X) {a : ℝ} (ha : 0 ≤ a)
    (hneg : Integrable (fun x => Real.exp (-a*dist p x)) μ)
    (hexp₀ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₀)
    (hexp₁ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν₁)
    (hd₀ : Integrable (fun x => dist p x^2) ν₀)
    (hd₁ : Integrable (fun x => dist p x^2) ν₁)
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (φ : X → ℝ) {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hrep : φ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (π : Measure (X×X)) (hπ₀ : π.map Prod.fst = ν₀) (hπ₁ : π.map Prod.snd = ν₁) :
    ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁) ≤
      (∫⁻x, localSlope φ x^2 ∂ν₀)^(1/(2:ℝ))*(transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  obtain ⟨plan,hp,_,ho,hw⟩ := FullCD.exists_HWI_exp_plan μ K n hcd ν₀ ν₁ h₀ h₁
    hm₀ hm₁ hEnt₀ hEnt₁ p ha hneg hexp₀ hexp₁ hd₀ hd₁ hpos φ hφ hrep
  let := hp
  have hD := optimalPlan_dist_sq_integrable ν₀ ν₁ plan ho p hd₀ hd₁
  let d : ℝ := ∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂plan
  have hd : 0 ≤ d := integral_nonneg (fun _ => sq_nonneg _)
  have hc : ENNReal.ofReal d ≤ transportCost π := by
    apply le_trans _ (ho.2.2 π hπ₀ hπ₁)
    rw [transportCost,lintegral_map
      ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2)
      ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    rw [show ENNReal.ofReal d = ∫⁻γ : C(Time,X), ENNReal.ofReal (dist (γ 0) (γ 1)^2) ∂plan from
      ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall fun _ => sq_nonneg _)]
    exact lintegral_mono (fun γ => (ENNReal.ofReal_pow dist_nonneg 2).le)
  have hdrop : ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁) ≤
      ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+(K/2)*d)+
      ENNReal.ofReal (|K|/2)*ENNReal.ofReal d := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ |K|/2)]
    calc
      _ ≤ ENNReal.ofReal ((boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+(K/2)*d)+
          (|K|/2)*d) := ENNReal.ofReal_le_ofReal (by nlinarith [neg_abs_le K])
      _ ≤ _ := ENNReal.ofReal_add_le
  calc
    _ ≤ ENNReal.ofReal (boltzmannEntropy μ ν₀-boltzmannEntropy μ ν₁+(K/2)*d)+
        ENNReal.ofReal (|K|/2)*ENNReal.ofReal d := hdrop
    _ ≤ (∫⁻x, localSlope φ x^2 ∂ν₀)^(1/(2:ℝ))*(ENNReal.ofReal d)^(1/(2:ℝ))+
        ENNReal.ofReal (|K|/2)*ENNReal.ofReal d := add_le_add hw le_rfl
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hc (by norm_num)))
      (mul_le_mul' le_rfl hc)
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X]
 theorem localSlope_log_sq_weighted_le {u : X → ℝ} {C : ℝ≥0}
    (hu : LipschitzWith C u) (x : X) (hx : 0 < u x) :
    localSlope (fun y => Real.log (u y^2)) x^2*ENNReal.ofReal (u x^2) ≤
      4*localSlope u x^2 := by
  have hd : HasDerivAt (fun a : ℝ => Real.log (a^2)) (2/u x) (u x) := by
    have hh := ((hasDerivAt_id (u x)).pow 2).log (pow_ne_zero 2 hx.ne')
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,mul_one] at hh
    apply hh.congr_deriv
    field_simp
  have hs := localSlope_comp_hasDerivAt hd hu.continuous.continuousAt
    (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hu x))
  have hc : ENNReal.ofReal (2/u x)^2*ENNReal.ofReal (u x^2) = 4 := by
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2/u x),← ENNReal.ofReal_mul (sq_nonneg _)]
    have he : (2/u x)^2*u x^2 = 4 := by field_simp; norm_num
    rw [he]
    norm_num
  simp only [Function.comp_def,abs_of_pos (show 0 < 2/u x by positivity)] at hs
  calc
    _ ≤ (ENNReal.ofReal (2/u x)*localSlope u x)^2*ENNReal.ofReal (u x^2) :=
      mul_le_mul' (pow_le_pow_left' hs 2) le_rfl
    _ = (ENNReal.ofReal (2/u x)^2*ENNReal.ofReal (u x^2))*localSlope u x^2 := by ring
    _ = _ := by rw [hc]

variable [MeasurableSpace X] [BorelSpace X]
 theorem log_sq_slope_integral_le {u : X → ℝ} {C : ℝ≥0}
    (μ : Measure X) (hu : LipschitzWith C u) (hpos : ∀ x, 0 < u x) :
    (∫⁻x, localSlope (fun y => Real.log (u y^2)) x^2 ∂μ.withDensity (fun x => ENNReal.ofReal (u x^2))) ≤
      4*(∫⁻x, localSlope u x^2 ∂μ) := by
  have hcont : Continuous (fun y => Real.log (u y^2)) :=
    (hu.continuous.pow 2).log (fun x => pow_ne_zero 2 (hpos x).ne')
  rw [lintegral_withDensity_eq_lintegral_mul μ
    (show Measurable (fun x => ENNReal.ofReal (u x^2)) from
      (hu.continuous.pow 2).measurable.ennreal_ofReal) ((localSlope_measurable hcont).pow_const 2)]
  calc
    _ ≤ ∫⁻x, 4*localSlope u x^2 ∂μ := by
      apply lintegral_mono
      intro x
      rw [mul_comm]
      exact localSlope_log_sq_weighted_le hu x (hpos x)
    _ = _ := lintegral_const_mul _ ((localSlope_measurable hu.continuous).pow_const 2)
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
omit [SeparableSpace X] in
 theorem log_sq_majorant_sqrt_le (μ : Measure X) {u : X → ℝ} {C : ℝ≥0}
    (hu : LipschitzWith C u) (hpos : ∀ x, 0 < u x) {G : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ u G) :
    (∫⁻x, localSlope (fun y => Real.log (u y^2)) x^2
      ∂μ.withDensity (fun x => ENNReal.ofReal (u x^2)))^(1/(2:ℝ)) ≤
      ENNReal.ofReal (2*‖G‖) := by
  have hb : (∫⁻x, localSlope u x^2 ∂μ) ≤ ENNReal.ofReal (‖G‖^2) := by
    rw [← lintegral_enorm_sq_Lp μ G]
    apply lintegral_mono_ae
    filter_upwards [hG] with x hx
    rw [Real.enorm_of_nonneg hx.1]
    exact pow_le_pow_left' hx.2 2
  have h := ENNReal.rpow_le_rpow ((log_sq_slope_integral_le μ hu hpos).trans
    (mul_le_mul' le_rfl hb)) (by norm_num : 0 ≤ 1/(2:ℝ))
  apply h.trans_eq
  rw [show (4:ℝ≥0∞)*ENNReal.ofReal (‖G‖^2) = ENNReal.ofReal ((2*‖G‖)^2) by
    rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring]
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by positivity)]

 

 theorem FullCD.sqrt_density_descent (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (u : X → ℝ) {C : ℝ≥0} (hu : LipschitzWith C u) (hpos : ∀ x, 0 < u x)
    (hlog : ∃ L : ℝ≥0, LipschitzWith L (fun x => Real.log (u x^2)))
    (G : Lp ℝ 2 μ) (hG : IsSlopeMajorant μ u G)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (u x^2))))
    (hm₀ : FiniteSecondMoment (μ.withDensity (fun x => ENNReal.ofReal (u x^2))))
    (hm₁ : FiniteSecondMoment ν)
    (he₀ : Integrable (fun x => u x^2*Real.log (u x^2)) μ)
    (he₁ : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (p : X) {a : ℝ} (ha : 0 ≤ a)
    (hn : Integrable (fun x => Real.exp (-a*dist p x)) μ)
    (hex₀ : Integrable (fun x => Real.exp ((3*a)*dist p x))
      (μ.withDensity (fun x => ENNReal.ofReal (u x^2))))
    (hex₁ : Integrable (fun x => Real.exp ((3*a)*dist p x)) ν)
    (hd₀ : Integrable (fun x => dist p x^2) (μ.withDensity (fun x => ENNReal.ofReal (u x^2))))
    (hd₁ : Integrable (fun x => dist p x^2) ν)
    (π : Measure (X×X))
    (hπ₀ : π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (u x^2)))
    (hπ₁ : π.map Prod.snd = ν) :
    ENNReal.ofReal ((∫x, u x^2*Real.log (u x^2) ∂μ)-boltzmannEntropy μ ν) ≤
      ENNReal.ofReal (2*‖G‖)*(transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  let := hprob
  have hr := Measure.rnDeriv_withDensity μ
    (show Measurable (fun x => ENNReal.ofReal (u x^2)) from (hu.continuous.pow 2).measurable.ennreal_ofReal)
  have hr' : (fun x => ((μ.withDensity (fun y => ENNReal.ofReal (u y^2))).rnDeriv μ x).toReal) =ᵐ[μ]
      fun x => u x^2 := hr.mono (fun x hx => by dsimp only at hx ⊢; rw [hx,ENNReal.toReal_ofReal (sq_nonneg _)])
  have he : Integrable (fun x => ((μ.withDensity (fun y => ENNReal.ofReal (u y^2))).rnDeriv μ x).toReal*
      Real.log ((μ.withDensity (fun y => ENNReal.ofReal (u y^2))).rnDeriv μ x).toReal) μ :=
    he₀.congr (hr'.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  obtain ⟨L,hL⟩ := hlog
  have h := FullCD.entropy_descent_le_coupling μ K n hcd _ ν
    (withDensity_absolutelyContinuous _ _) hν hm₀ hm₁ he he₁ p ha hn hex₀ hex₁ hd₀ hd₁
    (hr'.mono fun x hx => by dsimp only at hx ⊢; rw [hx]; exact sq_pos_of_pos (hpos x)) _ hL
    (hr'.mono fun x hx => by dsimp only at hx ⊢; rw [hx]) π hπ₀ hπ₁
  have heq : boltzmannEntropy μ (μ.withDensity (fun x => ENNReal.ofReal (u x^2))) =
      ∫x, u x^2*Real.log (u x^2) ∂μ := integral_congr_ae (hr'.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  rw [heq] at h
  exact h.trans (add_le_add (mul_le_mul' (log_sq_majorant_sqrt_le μ hu hpos hG) le_rfl) le_rfl)
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
 theorem squareDensity_probability {f : X → ℝ}
    (hi : Integrable (fun x => f x^2) μ) (hm : ∫x, f x^2 ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x^2))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _),hm,ENNReal.ofReal_one]
 theorem squareDensity_integrable_iff {f v : X → ℝ} (hf : Measurable f) :
    Integrable v (μ.withDensity (fun x => ENNReal.ofReal (f x^2))) ↔
      Integrable (fun x => f x^2*v x) μ := by
  have h := integrable_withDensity_iff_integrable_smul₀' (μ := μ)
    (show AEMeasurable (fun x => ENNReal.ofReal (f x^2)) μ from (hf.pow_const 2).ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (g := v)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul] using h
 theorem squareDensity_entropy [SigmaFinite μ] {f : X → ℝ} (hf : Measurable f) :
    boltzmannEntropy μ (μ.withDensity (fun x => ENNReal.ofReal (f x^2))) =
      ∫x, f x^2*Real.log (f x^2) ∂μ := by
  have hr := Measure.rnDeriv_withDensity μ (show Measurable (fun x => ENNReal.ofReal (f x^2)) from
    (hf.pow_const 2).ennreal_ofReal)
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  rw [hx,ENNReal.toReal_ofReal (sq_nonneg _)]
end

 
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [NeZero μ]
 

 theorem exists_normalized_exponential_sqrt (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R)) :
    ∃ (c : ℝ) (H : Lp ℝ 2 μ), 0 < c ∧
      let g := fun x => c*Real.exp (-(2*(B+1))*dist p x)
      IsSlopeMajorant μ g H ∧ Integrable (fun x => g x^2) μ ∧
      (∫x, g x^2 ∂μ) = 1 ∧ Integrable (fun x => g x^2*Real.log (g x^2)) μ ∧
      Integrable (fun x => Real.exp ((3*(B+1))*dist p x))
        (μ.withDensity (fun x => ENNReal.ofReal (g x^2))) ∧
      Integrable (fun x => dist p x^2) (μ.withDensity (fun x => ENNReal.ofReal (g x^2))) := by
  let b := 2*(B+1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let e := fun x => Real.exp (-(2*b)*dist p x)
  have hi : Integrable e μ := integrable_exp_neg_dist_of_volume μ p hA hB (by dsimp [b]; linarith) hvol
  let z := ∫x, e x ∂μ
  have hz : 0 < z := integral_exp_pos hi
  let c := Real.sqrt z⁻¹
  have hc : 0 < c := Real.sqrt_pos.mpr (inv_pos.mpr hz)
  have hcsq : c^2 = z⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hz.le)
  let g := fun x => c*Real.exp (-b*dist p x)
  have hgsq (x : X) : g x^2 = c^2*e x := by
    dsimp [g,e]
    rw [mul_pow,← Real.exp_nat_mul]
    congr 2
    ring
  have hgm : Measurable g :=
    ((lipschitzWith_const_mul_real (exp_neg_dist_lipschitz p hb) c).continuous.measurable)
  have hgI : Integrable (fun x => g x^2) μ := by
    simpa only [hgsq] using hi.const_mul (c^2)
  have hgM : (∫x, g x^2 ∂μ) = 1 := by
    simp only [hgsq,integral_const_mul]
    change c^2*z = 1
    rw [hcsq,inv_mul_cancel₀ hz.ne']
  let H := c • (b • (exp_neg_dist_memLp_two μ p b hi).toLp _)
  have hG : IsSlopeMajorant μ g H :=
    (exp_neg_dist_slopeMajorant μ p hb hi).const_mul μ hc.le
  have hI1 : Integrable (fun x => dist p x*e x) μ := by
    simpa only [pow_one] using integrable_dist_pow_mul_exp_of_le μ p hA hB hvol 1
      (by dsimp [b]; norm_num; linarith : B+(1:ℕ)+1 ≤ 2*b)
  have hI2 : Integrable (fun x => dist p x^2*e x) μ :=
    integrable_dist_pow_mul_exp_of_le μ p hA hB hvol 2 (by dsimp [b]; linarith)
  have heq (x : X) : g x^2*Real.log (g x^2) =
      (c^2*Real.log (c^2))*e x-(2*b*c^2)*(dist p x*e x) := by
    rw [hgsq,Real.log_mul (pow_ne_zero 2 hc.ne') (Real.exp_ne_zero _),Real.log_exp]
    dsimp [e]
    ring
  have hgE : Integrable (fun x => g x^2*Real.log (g x^2)) μ := by
    convert (hi.const_mul (c^2*Real.log (c^2))).sub (hI1.const_mul (2*b*c^2)) using 1
    funext x
    exact heq x
  have hExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x))
      (μ.withDensity (fun x => ENNReal.ofReal (g x^2))) := by
    apply (squareDensity_integrable_iff μ hgm).mpr
    have hi' := integrable_exp_neg_dist_of_volume μ p hA hB (by linarith : B < B+1) hvol
    convert hi'.const_mul (c^2) using 1
    funext x
    rw [hgsq,mul_assoc]
    dsimp [e]
    rw [← Real.exp_add]
    congr 2
    dsimp [b]
    ring
  have hDist : Integrable (fun x => dist p x^2)
      (μ.withDensity (fun x => ENNReal.ofReal (g x^2))) := by
    apply (squareDensity_integrable_iff μ hgm).mpr
    convert hI2.const_mul (c^2) using 1
    funext x
    rw [hgsq]
    ring
  exact ⟨c,H,hc,hG,hgI,hgM,hgE,hExp,hDist⟩

end RegularPointCoordinates

end OAI
