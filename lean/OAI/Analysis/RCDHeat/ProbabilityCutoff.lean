import Mathlib
import OAI.Analysis.RCDHeat.HeatMetricSpeed
import OAI.Analysis.RCDHeat.NormalizedCutoff

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: ProbabilityCutoff, DensityFactorLaws, EntropyCutoff, HeatGeneralHWI, HeatFiniteHWI, HeatFullHWI. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 

 theorem probability_cutoff_factors (ν : Measure X) [IsProbabilityMeasure ν] (p : X) :
    ∃ (ws : ℕ → X → ℝ) (Rs : ℕ → ℝ),
      (∀ i, Measurable (ws i)) ∧
      (∀ i x, 0 ≤ ws i x ∧ ws i x ≤ 2) ∧
      (∀ i x, ws i x ≠ 0 → dist p x ≤ Rs i) ∧
      (∀ x, Tendsto (fun i => ws i x) atTop (𝓝 1)) ∧
      (∀ i, Integrable (ws i) ν) ∧ (∀ i, ∫x, ws i x ∂ν = 1) := by
  let R : ℕ → ℝ := fun i => (i:ℝ)+1
  have hR (i : ℕ) : 0 < R i := by dsimp [R]; positivity
  have hRL : Tendsto R atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  let θ := fun i => radialCutoff p (R i)
  have hθm (i : ℕ) : Measurable (θ i) := (radialCutoff_lipschitz p (hR i)).continuous.measurable
  have hθi (i : ℕ) : Integrable (θ i) ν := (integrable_const (1:ℝ)).mono' (hθm i).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_bounds p (R i) x).1]
      exact (radialCutoff_bounds p (R i) x).2)
  have hθL (x : X) : Tendsto (fun i => θ i x) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hRL.eventually (radialCutoff_eventually_one p x)] with i hi
    exact hi.symm
  have hmass : Tendsto (fun i => ∫x, θ i x ∂ν) atTop (𝓝 (1:ℝ)) := by
    have hh := (integral_radialCutoff_tendsto ν p (fun _ : X => (1:ℝ)) (integrable_const _)).comp hRL
    simpa only [θ,Function.comp_def,one_mul,integral_const,probReal_univ,one_smul] using hh
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmass.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
  let a : ℕ → ℝ := fun i => (∫x, θ (i+N) x ∂ν)⁻¹
  have hnu (i : ℕ) : (1:ℝ)/2 < ∫x, θ (i+N) x ∂ν := hN _ (Nat.le_add_left N i)
  have hnpos (i : ℕ) : 0 < ∫x, θ (i+N) x ∂ν := by linarith [hnu i]
  have haP (i : ℕ) : 0 < a i := inv_pos.mpr (hnpos i)
  have haB (i : ℕ) : a i ≤ 2 := by
    dsimp [a]
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ (hnpos i) (by norm_num)).mpr (hnu i).le
      _ = 2 := by norm_num
  have haL : Tendsto a atTop (𝓝 (1:ℝ)) := by
    simpa only [a,Function.comp_def,inv_one] using (hmass.comp (tendsto_add_atTop_nat N)).inv₀ one_ne_zero
  refine ⟨fun i x => a i*θ (i+N) x,fun i => 2*R (i+N),?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact measurable_const.mul (hθm (i+N))
  · intro i x
    have hb := radialCutoff_bounds p (R (i+N)) x
    refine ⟨mul_nonneg (haP i).le hb.1,?_⟩
    exact (mul_le_mul (haB i) hb.2 hb.1 (by norm_num)).trans_eq (mul_one _)
  · intro i x hx
    by_contra hn
    apply hx
    dsimp only
    rw [show θ (i+N) x = 0 from radialCutoff_eq_zero p (hR (i+N)) (le_of_not_ge hn),mul_zero]
  · intro x
    simpa only [Function.comp_def,mul_one] using haL.mul ((hθL x).comp (tendsto_add_atTop_nat N))
  · intro i
    exact (hθi (i+N)).const_mul (a i)
  · intro i
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (ne_of_gt (hnpos i))
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
 theorem realDensity_probability {f : X → ℝ} (hi : Integrable f μ)
    (hf : 0 ≤ᵐ[μ] f) (hm : ∫x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hf,hm,ENNReal.ofReal_one]
 theorem realDensity_entropy [SigmaFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ᵐx ∂μ, 0 ≤ f x) :
    boltzmannEntropy μ (μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫x, f x*Real.log (f x) ∂μ := by
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity μ hf.ennreal_ofReal,hfn] with x hx hn
  rw [hx,ENNReal.toReal_ofReal hn]
 theorem withDensity_real_rnDeriv [SigmaFinite μ] (ν : Measure X) [IsFiniteMeasure ν]
    (hν : ν ≪ μ) :
    μ.withDensity (fun x => ENNReal.ofReal (ν.rnDeriv μ x).toReal) = ν := by
  calc
    _ = μ.withDensity (ν.rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = ν := Measure.withDensity_rnDeriv_eq ν μ hν
 theorem density_factor_entropy_integrable {q w : X → ℝ} (hq : Measurable q)
    (hqn : ∀ᵐx ∂μ, 0 ≤ q x) (hqi : Integrable q μ)
    (hqe : Integrable (fun x => q x*Real.log (q x)) μ)
    (hw : Measurable w) (C : ℝ≥0) (hb : ∀ᵐx ∂μ, 0 ≤ w x ∧ w x ≤ C) :
    Integrable (fun x => (w x*q x)*Real.log (w x*q x)) μ := by
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) C)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  apply ((hqe.abs.const_mul C).add (hqi.const_mul |D|)).mono'
    (Real.continuous_mul_log.measurable.comp (hw.mul hq)).aestronglyMeasurable
  filter_upwards [hb,hqn] with x hx hqx
  simp only [Pi.add_apply,Function.comp_def,Pi.mul_apply]
  rw [Real.norm_eq_abs,mul_log_mul]
  calc
    _ ≤ |w x*(q x*Real.log (q x))|+|(w x*Real.log (w x))*q x| := abs_add_le _ _
    _ = w x*|q x*Real.log (q x)|+|w x*Real.log (w x)| *q x := by
      simp only [abs_mul,abs_of_nonneg hx.1,abs_of_nonneg hqx]
    _ ≤ _ := by
      apply add_le_add (mul_le_mul_of_nonneg_right hx.2 (abs_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hqx
      have hd : |w x*Real.log (w x)| ≤ D := by
        simpa only [Real.norm_eq_abs] using hD (w x) hx
      exact hd.trans (le_abs_self D)
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 

 theorem entropy_cutoff_recovery (μ : Measure X) [SigmaFinite μ]
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (p : X) :
    ∃ (rs : ℕ → X → ℝ≥0∞) (Rs : ℕ → ℝ),
      (∀ i, Measurable (rs i)) ∧ (∀ i x, rs i x ≠ ∞) ∧
      (∀ i x, rs i x ≤ 2*ENNReal.ofReal (ν.rnDeriv μ x).toReal) ∧
      (∀ i x, rs i x ≠ 0 → dist p x ≤ Rs i) ∧
      (∀ i, IsProbabilityMeasure (μ.withDensity (rs i))) ∧
      (∀ i, Integrable (fun x => ((μ.withDensity (rs i)).rnDeriv μ x).toReal *
        Real.log ((μ.withDensity (rs i)).rnDeriv μ x).toReal) μ) ∧
      Tendsto (fun i => boltzmannEntropy μ (μ.withDensity (rs i))) atTop (𝓝 (boltzmannEntropy μ ν)) ∧
      (∀ x, Tendsto (fun i => rs i x) atTop (𝓝 (ENNReal.ofReal (ν.rnDeriv μ x).toReal))) := by
  let q : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hq : Measurable q := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hqn (x : X) : 0 ≤ q x := ENNReal.toReal_nonneg
  have hqi : Integrable q μ := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν Set.univ))
  have hqe : μ.withDensity (fun x => ENNReal.ofReal (q x)) = ν := withDensity_real_rnDeriv μ ν hν
  obtain ⟨ws,Rs,hw,hwB,hwS,hwL,hwi,hwM⟩ := probability_cutoff_factors ν p
  let rs := fun i x => ENNReal.ofReal (ws i x*q x)
  have hrs (i : ℕ) : Measurable (rs i) := ((hw i).mul hq).ennreal_ofReal
  have hrn (i : ℕ) : (fun x => ((μ.withDensity (rs i)).rnDeriv μ x).toReal) =ᵐ[μ]
      fun x => ws i x*q x := by
    filter_upwards [Measure.rnDeriv_withDensity μ (hrs i)] with x hx
    rw [hx]
    exact ENNReal.toReal_ofReal (mul_nonneg (hwB i x).1 (hqn x))
  have hm (i : ℕ) : μ.withDensity (rs i) = ν.withDensity (fun x => ENNReal.ofReal (ws i x)) := by
    rw [← hqe,← withDensity_mul μ hq.ennreal_ofReal (hw i).ennreal_ofReal]
    congr 1
    funext x
    simp only [rs,Pi.mul_apply,ENNReal.ofReal_mul (hwB i x).1,mul_comm]
  have hEnt (i : ℕ) : boltzmannEntropy μ (μ.withDensity (rs i)) =
      ∫x, (ws i x*q x)*Real.log (ws i x*q x) ∂μ :=
    realDensity_entropy μ ((hw i).mul hq) (Eventually.of_forall fun x => mul_nonneg (hwB i x).1 (hqn x))
  refine ⟨rs,Rs,hrs,fun _ _ => ENNReal.ofReal_ne_top,?_,?_,?_,?_,?_,?_⟩
  · intro i x
    dsimp only [rs]
    rw [ENNReal.ofReal_mul (hwB i x).1]
    exact mul_le_mul' ((ENNReal.ofReal_le_ofReal (hwB i x).2).trans_eq (by norm_num)) le_rfl
  · intro i x hx
    apply hwS i x
    intro hz
    exact hx (by simp only [rs,hz,zero_mul,ENNReal.ofReal_zero])
  · intro i
    rw [hm i]
    exact realDensity_probability ν (hwi i) (Eventually.of_forall fun x => (hwB i x).1) (hwM i)
  · intro i
    apply (density_factor_entropy_integrable μ hq (Eventually.of_forall hqn) hqi hνE (hw i) 2
      (Eventually.of_forall (hwB i))).congr
    filter_upwards [hrn i] with x hx
    rw [hx]
  · have hh := density_factor_entropy_tendsto μ hq (Eventually.of_forall hqn) hqi hνE hw 2
      (fun i => Eventually.of_forall (hwB i)) (Eventually.of_forall hwL)
    simp_rw [hEnt]
    exact hh
  · intro x
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hwL x).mul_const (q x))
    simpa only [Function.comp_def,one_mul] using hh
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem FullCD.heat_wasserstein_HWI (μ : Measure X) [μ.Regular]
    [NeZero μ] [SigmaFinite μ]
    (hQ : QuadraticCheegerEnergy μ) (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfM : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    {t : ℝ} (ht : 0 < t) (hI : fisherInformation μ hQ f t ≠ ∞)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x)) ν)
    (hνDist : Integrable (fun x => dist p x^2) ν) :
    boltzmannEntropy μ (heatMeasure μ hQ t f)-boltzmannEntropy μ ν ≤
      Real.sqrt (fisherInformation μ hQ f t).toReal *
        (wassersteinEDist (heatMeasure μ hQ t f) ν).toReal+
      (|K|/2)*(wassersteinEDist (heatMeasure μ hQ t f) ν).toReal^2 := by
  have hfi := lp_integrable_of_bounded_support μ f p hfS
  let : IsProbabilityMeasure (heatMeasure μ hQ t f) :=
    heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfM ht.le
  have hm0 : FiniteSecondMoment (heatMeasure μ hQ t f) := heatAt_finiteSecondMoment μ hQ p hA hB hvol f hf0 hfS ht.le
  have hm1 : FiniteSecondMoment ν := finiteSecondMoment_of_integrable_dist ν p hνDist
  obtain ⟨plan,_,_,ho,_⟩ := hcd _ ν inferInstance inferInstance
    (heatMeasure_absolutelyContinuous μ hQ t f) hν hm0 hm1
  have hcfin := finite_second_moment_cost hm0 hm1 ho.1 ho.2.1
  have hh := hcd.heat_HWI μ hQ K n p hA hB hvol f hf0 hfM hfS C hfC ht hI ν hν
    hνE hνExp hνDist _ ho.1 ho.2.1
  have hpowfin : transportCost (plan.map (fun γ => (γ 0,γ 1)))^(1/(2:ℝ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hcfin
  have h1fin : ENNReal.ofReal (Real.sqrt (fisherInformation μ hQ f t).toReal)*
      transportCost (plan.map (fun γ => (γ 0,γ 1)))^(1/(2:ℝ)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpowfin
  have h2fin : ENNReal.ofReal (|K|/2)*transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin
  have hr := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.mpr ⟨h1fin,h2fin⟩)).mp hh
  rw [ENNReal.toReal_add h1fin h2fin,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),ENNReal.toReal_ofReal (by positivity : 0 ≤ |K|/2),
    ← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow] at hr
  simp only [wassersteinEDist,wassersteinSq_eq_cost ho,← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow,
    Real.sq_sqrt ENNReal.toReal_nonneg]
  exact hr
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
 

 theorem FullCD.heat_HWI_finite (μ : Measure X) [μ.Regular]
    [NeZero μ] [SigmaFinite μ]
    (hQ : QuadraticCheegerEnergy μ) (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfM : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    {t : ℝ} (ht : 0 < t) (hI : fisherInformation μ hQ f t ≠ ∞)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνDist : Integrable (fun x => dist p x^2) ν)
    (π : Measure (X×X))
    (hπ₀ : π.map Prod.fst = heatMeasure μ hQ t f) (hπ₁ : π.map Prod.snd = ν) :
    ENNReal.ofReal (boltzmannEntropy μ (heatMeasure μ hQ t f)-boltzmannEntropy μ ν) ≤
      ENNReal.ofReal (Real.sqrt (fisherInformation μ hQ f t).toReal)*
        (transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  have hfi := lp_integrable_of_bounded_support μ f p hfS
  let ρ := heatMeasure μ hQ t f
  let : IsProbabilityMeasure ρ := heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfM ht.le
  let : IsProbabilityMeasure π := by
    have : IsProbabilityMeasure (π.map Prod.snd) := by rwa [hπ₁]
    exact Measure.isProbabilityMeasure_of_map measurable_snd.aemeasurable
  have hρDist : Integrable (fun x => dist p x^2) ρ := heatMeasure_dist_sq_integrable μ hQ p hA hB hvol f hf0 hfS ht.le
  let q := fun x => ENNReal.ofReal (ν.rnDeriv μ x).toReal
  have hq : Measurable q := (Measure.measurable_rnDeriv ν μ).ennreal_toReal.ennreal_ofReal
  have hqe : μ.withDensity q = ν := withDensity_real_rnDeriv μ ν hν
  obtain ⟨rs,Rs,hrs,_,hrsB,hrsS,hrsP,hrsE,hrsEnt,hrsL⟩ := entropy_cutoff_recovery μ ν hν hνE p
  have hqint : (∫⁻x, q x*ENNReal.ofReal (dist p x)^2 ∂μ) ≠ ∞ := by
    change (∫⁻x, (q * fun x : X => ENNReal.ofReal (dist p x)^2) x ∂μ) ≠ ∞
    rw [← lintegral_withDensity_eq_lintegral_mul μ hq
      (by fun_prop : Measurable (fun x : X => ENNReal.ofReal (dist p x)^2)),hqe]
    have hh := (lintegral_ofReal_ne_top_iff_integrable hνDist.aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _)).mpr hνDist
    simpa only [ENNReal.ofReal_pow dist_nonneg] using hh
  have hρint : (∫⁻x, ENNReal.ofReal (dist p x)^2 ∂ρ) ≠ ∞ := by
    have hh := (lintegral_ofReal_ne_top_iff_integrable hρDist.aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _)).mpr hρDist
    simpa only [ENNReal.ofReal_pow dist_nonneg] using hh
  have hs0 : (π.map Prod.swap).map Prod.fst = μ.withDensity q := by
    rw [Measure.map_map measurable_fst measurable_swap,hqe]
    exact hπ₁
  have hs1 : (π.map Prod.swap).map Prod.snd = ρ := by
    rw [Measure.map_map measurable_snd measurable_swap]
    exact hπ₀
  let : IsProbabilityMeasure (π.map Prod.swap) := inferInstance
  obtain ⟨plans,costs,hp0,hp1,hpc,hCost⟩ := dominated_density_coupling_recovery μ ρ
    (π.map Prod.swap) hq (fun _ => ENNReal.ofReal_ne_top) hrs hrsP hs0 hs1
    (Eventually.of_forall hrsL) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
    (fun i => Eventually.of_forall (hrsB i)) p hqint hρint
  rw [transportCost_swap] at hCost
  have hineq (i : ℕ) :
      ENNReal.ofReal (boltzmannEntropy μ ρ-boltzmannEntropy μ (μ.withDensity (rs i))) ≤
        ENNReal.ofReal (Real.sqrt (fisherInformation μ hQ f t).toReal)*(costs i)^(1/(2:ℝ))+
        ENNReal.ofReal (|K|/2)*costs i := by
    let := hrsP i
    have hs : ∀ᵐx ∂μ.withDensity (rs i), dist p x ≤ Rs i :=
      (ae_withDensity_iff (hrs i)).mpr (Eventually.of_forall (hrsS i))
    have hdist : Integrable (fun x => dist p x^2) (μ.withDensity (rs i)) := by
      apply (integrable_const ((max (Rs i) 0)^2)).mono' (by fun_prop)
      filter_upwards [hs] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ dist_nonneg (hx.trans (le_max_left _ _)) 2
    have hexp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x)) (μ.withDensity (rs i)) := by
      apply (integrable_const (Real.exp ((3*(B+1))*Rs i))).mono' (by fun_prop)
      filter_upwards [hs] with x hx
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (by positivity))
    have hp0' : ((plans i).map Prod.swap).map Prod.fst = heatMeasure μ hQ t f := by
      rw [Measure.map_map measurable_fst measurable_swap]
      exact hp1 i
    have hp1' : ((plans i).map Prod.swap).map Prod.snd = μ.withDensity (rs i) := by
      rw [Measure.map_map measurable_snd measurable_swap]
      exact hp0 i
    have hh := hcd.heat_HWI μ hQ K n p hA hB hvol f hf0 hfM hfS C hfC ht hI
      (μ.withDensity (rs i)) (withDensity_absolutelyContinuous μ (rs i)) (hrsE i)
      hexp hdist ((plans i).map Prod.swap) hp0' hp1'
    rw [transportCost_swap] at hh
    apply hh.trans
    gcongr <;> exact hpc i
  have hLeft := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := boltzmannEntropy μ ρ)).sub hrsEnt)
  have hSqrt := (ENNReal.continuous_rpow_const (y := (1/(2:ℝ)))).continuousAt.tendsto.comp hCost
  have hRight := (ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (Real.sqrt (fisherInformation μ hQ f t).toReal)) hSqrt
    (Or.inr ENNReal.ofReal_ne_top)).add
    (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (|K|/2)) hCost (Or.inr ENNReal.ofReal_ne_top))
  exact le_of_tendsto_of_tendsto hLeft hRight (Eventually.of_forall hineq)
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem FullCD.heat_wasserstein_HWI_finite (μ : Measure X) [μ.Regular]
    [NeZero μ] [SigmaFinite μ]
    (hQ : QuadraticCheegerEnergy μ) (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfM : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    {t : ℝ} (ht : 0 < t) (hI : fisherInformation μ hQ f t ≠ ∞)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνDist : Integrable (fun x => dist p x^2) ν) :
    boltzmannEntropy μ (heatMeasure μ hQ t f)-boltzmannEntropy μ ν ≤
      Real.sqrt (fisherInformation μ hQ f t).toReal *
        (wassersteinEDist (heatMeasure μ hQ t f) ν).toReal+
      (|K|/2)*(wassersteinEDist (heatMeasure μ hQ t f) ν).toReal^2 := by
  have hfi := lp_integrable_of_bounded_support μ f p hfS
  let : IsProbabilityMeasure (heatMeasure μ hQ t f) :=
    heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfM ht.le
  have hm0 : FiniteSecondMoment (heatMeasure μ hQ t f) := heatAt_finiteSecondMoment μ hQ p hA hB hvol f hf0 hfS ht.le
  have hm1 : FiniteSecondMoment ν := finiteSecondMoment_of_integrable_dist ν p hνDist
  obtain ⟨plan,_,_,ho,_⟩ := hcd _ ν inferInstance inferInstance
    (heatMeasure_absolutelyContinuous μ hQ t f) hν hm0 hm1
  have hcfin := finite_second_moment_cost hm0 hm1 ho.1 ho.2.1
  have hh := hcd.heat_HWI_finite μ hQ K n p hA hB hvol f hf0 hfM hfS C hfC ht hI ν hν
    hνE hνDist _ ho.1 ho.2.1
  have hpowfin : transportCost (plan.map (fun γ => (γ 0,γ 1)))^(1/(2:ℝ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hcfin
  have h1fin : ENNReal.ofReal (Real.sqrt (fisherInformation μ hQ f t).toReal)*
      transportCost (plan.map (fun γ => (γ 0,γ 1)))^(1/(2:ℝ)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpowfin
  have h2fin : ENNReal.ofReal (|K|/2)*transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin
  have hr := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.mpr ⟨h1fin,h2fin⟩)).mp hh
  rw [ENNReal.toReal_add h1fin h2fin,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),ENNReal.toReal_ofReal (by positivity : 0 ≤ |K|/2),
    ← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow] at hr
  simp only [wassersteinEDist,wassersteinSq_eq_cost ho,← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow,
    Real.sq_sqrt ENNReal.toReal_nonneg]
  exact hr

end RegularPointCoordinates

end OAI
