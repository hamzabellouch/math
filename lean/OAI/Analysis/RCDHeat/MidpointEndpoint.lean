import Mathlib
import OAI.Analysis.RCDHeat.DimensionalEntropy

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: MidpointEndpoint, PlanEntropyEndpoint, RawEntropyVariation, SqrtCorePlanVariation, DimensionalCore. -/



namespace RegularPointCoordinates

section

 

open Set Filter
open scoped Topology

theorem dimensional_midpoint_endpoint (E A B : ℝ → ℝ) {N κ M a b : ℝ}
    (hN : 0 < N) (hE0 : ContinuousAt E 0) (hE1 : ContinuousAt E 1)
    (hmid : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      E ((x+y)/2) ≤ (E x+E y)/2-κ*(x-y)^2/8-
        N*Real.log (Real.cosh ((E x-E y)/(2*N))))
    (hA : Tendsto A (𝓝[>] (0:ℝ)) (𝓝 a))
    (hB : Tendsto B (𝓝[>] (0:ℝ)) (𝓝 b))
    (hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      A t ≤ (E t-E 0)/t+t*M ∧ B t ≤ (E (1-t)-E 1)/t+t*M) :
    κ+(E 1-E 0)^2/N ≤ -a-b := by
  let t : ℕ → ℝ := fun k => 1/((k:ℝ)+2)
  let δ : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have ht : Tendsto t atTop (𝓝 (0:ℝ)) := by
    have h : Tendsto (fun k : ℕ => ((k:ℝ)+2)⁻¹) atTop (𝓝 (0:ℝ)) :=
      tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (2:ℝ))))
    simpa only [t,one_div] using h
  have hδ : Tendsto δ atTop (𝓝 (0:ℝ)) := by
    have h : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
      tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (1:ℝ))))
    simpa only [δ,one_div] using h
  have htpos (k : ℕ) : 0 < t k := by dsimp [t]; positivity
  have ht' : Tendsto t atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htpos⟩
  let d : ℕ → ℝ := fun k => E 1+E (1-t k)-E (t k)-E 0
  have hEt : Tendsto (fun k => E (t k)) atTop (𝓝 (E 0)) := hE0.tendsto.comp ht
  have hEr : Tendsto (fun k => E (1-t k)) atTop (𝓝 (E 1)) := by
    apply hE1.tendsto.comp
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub ht
  have hd : Tendsto d atTop (𝓝 (2*(E 1-E 0))) := by
    convert ((tendsto_const_nhds (x := E 1)).add hEr).sub hEt |>.sub_const (E 0) using 1
    ring_nf
  let g : ℕ → ℝ := fun k => κ*(1-t k)+(1+δ k)*
    (2*N*(d k)^2/(4*N^2)*logCoshRatio (d k*δ k/(2*N)))
  have hg : Tendsto g atTop (𝓝 (κ+(E 1-E 0)^2/N)) := by
    have hsq := dimensional_log_cosh_scaled_limit d δ hd hδ N hN.ne'
    have hh := ((tendsto_const_nhds (x := κ)).mul
      ((tendsto_const_nhds (x := (1:ℝ))).sub ht)).add
      (((tendsto_const_nhds (x := (1:ℝ))).add hδ).mul hsq)
    have he : κ*(1-(0:ℝ))+(1+(0:ℝ))*((2*(E 1-E 0))^2/(4*N)) =
        κ+(E 1-E 0)^2/N := by ring
    rw [he] at hh
    exact hh
  have hright : Tendsto (fun k => -A (t k)-B (t k)+2*t k*M)
      atTop (𝓝 (-a-b)) := by
    simpa using (((hA.comp ht').neg.sub (hB.comp ht')).add
      (((tendsto_const_nhds (x := (2:ℝ))).mul ht).mul_const M))
  apply le_of_tendsto_of_tendsto hg hright
  filter_upwards [ht'.eventually hbound] with k hk
  have hgrid := dimensional_midpoint_grid E hN hmid (k+1) (by omega)
  have hk1 : (k:ℝ)+1 ≠ 0 := by positivity
  have hk2 : (k:ℝ)+2 ≠ 0 := by positivity
  have hN0 := hN.ne'
  have he : g k = κ*((k:ℝ)+1)/((k:ℝ)+2)+
      2*N*((k:ℝ)+1)*((k:ℝ)+2)*Real.log (Real.cosh (d k/(2*N*((k:ℝ)+1)))) := by
    rw [log_cosh_eq_sq_mul_ratio]
    dsimp only [g,δ,t]
    have hearg : d k/(2*N*((k:ℝ)+1)) = d k*(1/((k:ℝ)+1))/(2*N) := by
      field_simp
    rw [hearg]
    field_simp
    ring
  have hegrid : κ*((k:ℝ)+1)/((k:ℝ)+2)+
      2*N*((k:ℝ)+1)*((k:ℝ)+2)*Real.log (Real.cosh (d k/(2*N*((k:ℝ)+1)))) ≤
        (E 0-E (t k)+E 1-E (1-t k))/t k := by
    simpa only [Nat.cast_add,Nat.cast_one,show (k:ℝ)+1+1 = (k:ℝ)+2 by ring,
      d,t,one_div,div_inv_eq_mul] using hgrid
  rw [he]
  apply hegrid.trans
  have hsum := add_le_add hk.1 hk.2
  have hfrac : (E 0-E (t k)+E 1-E (1-t k))/t k =
      -((E (t k)-E 0)/t k+(E (1-t k)-E 1)/t k) := by ring
  rw [hfrac]
  linarith only [hsum]

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_plan_dimensional_endpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ s : Time,
      plan.map (fun γ => γ s) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ s : Time, ∀ᵐ x ∂plan.map (fun γ => γ s), dist x p ≤ R)
    (N : ℝ) (hN : (n:ℝ) ≤ N) (A B : ℝ → ℝ) {a b M : ℝ}
    (hA : Tendsto A (𝓝[>] (0:ℝ)) (𝓝 a))
    (hB : Tendsto B (𝓝[>] (0:ℝ)) (𝓝 b))
    (hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      A t ≤ (entropyPlanExtension (hausdorff n X) plan t-
        boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 0)))/t+t*M ∧
      B t ≤ (entropyPlanExtension (hausdorff n X) plan (1-t)-
        boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 1)))/t+t*M) :
    K*(wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal+
      (boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 1))-
       boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 0)))^2/N ≤ -a-b := by
  let μ := hausdorff n X
  let E := entropyPlanExtension μ plan
  have he (t : Time) : E t = boltzmannEntropy μ (plan.map (fun γ => γ t)) :=
    entropyPlanExtension_eq μ plan t
  have hE0 : ContinuousAt E 0 := by
    have hh : ContinuousAt
        (fun t : Time => boltzmannEntropy μ (plan.map (fun γ => γ t)))
        (Set.projIcc 0 1 zero_le_one 0) := by
      have h0 : Set.projIcc (0:ℝ) 1 zero_le_one 0 = (0:Time) := by
        apply Subtype.ext
        simp
      rw [h0]
      exact hX.entropy_compressed_plan_continuousAt_zero K n hn plan hg hp C hc p hR hs
    exact hh.comp (continuous_projIcc.continuousAt (x := (0:ℝ)))
  have hE1 : ContinuousAt E 1 := by
    have hh : ContinuousAt
        (fun t : Time => boltzmannEntropy μ (plan.map (fun γ => γ t)))
        (Set.projIcc 0 1 zero_le_one 1) := by
      have h1 : Set.projIcc (0:ℝ) 1 zero_le_one 1 = (1:Time) := by
        apply Subtype.ext
        simp
      rw [h1]
      exact hX.entropy_compressed_plan_continuousAt_one K n hn plan hg hp C hc p hR hs
    exact hh.comp (continuous_projIcc.continuousAt (x := (1:ℝ)))
  have hmid : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      E ((x+y)/2) ≤ (E x+E y)/2-
        (K*(wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal)*(x-y)^2/8-
        N*Real.log (Real.cosh ((E x-E y)/(2*N))) := by
    intro x hx y hy
    let x' : Time := ⟨x,hx⟩
    let y' : Time := ⟨y,hy⟩
    have hm : (x+y)/2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
    have hte : timeSegment x' y' midpointTime = (⟨(x+y)/2,hm⟩ : Time) := by
      apply Subtype.ext
      dsimp [timeSegment,midpointTime,x',y']
      ring
    have hh := hX.compressed_plan_dimensional_entropy_submidpoint K n hn plan hg hp C hc p hR hs N hN x' y'
    rw [hte] at hh
    rw [show E x = E x' from rfl,he x',show E y = E y' from rfl,he y',
      show E ((x+y)/2) = E (⟨(x+y)/2,hm⟩ : Time) from rfl,he]
    convert hh using 1
    ring
  have hNpos : 0 < N := lt_of_lt_of_le (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hn) hN
  have hbnd : ∀ᶠ t in 𝓝[>] (0:ℝ), A t ≤ (E t-E 0)/t+t*M ∧ B t ≤ (E (1-t)-E 1)/t+t*M := by
    simpa only [show (0:ℝ) = ((0:Time):ℝ) from rfl,show (1:ℝ) = ((1:Time):ℝ) from rfl,he] using hbound
  have hh := dimensional_midpoint_endpoint E A B hNpos hE0 hE1 hmid hA hB hbnd
  simpa only [show (0:ℝ) = ((0:Time):ℝ) from rfl,show (1:ℝ) = ((1:Time):ℝ) from rfl,he] using hh

end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem entropy_regularized_raw_plan_secant (μ : Measure X) [SigmaFinite μ]
    (ν₀ : Measure X) [IsProbabilityMeasure ν₀]
    (r : Lp ℝ 2 μ) {h : X → ℝ} (hh : Measurable h)
    (hr : (r : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (hrn : (fun x => h x^2) =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    (t : Time) (ht : 0 < (t:ℝ))
    (het : Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ) :
    regularizedPlanLogSecant π h t ≤
      (boltzmannEntropy μ (π.map (fun γ => γ t))-boltzmannEntropy μ ν₀)/(t:ℝ) +
        (t:ℝ)*(μ B).toReal := by
  have hν (s : Time) : π.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have hνB (s : Time) : π.map (fun γ => γ s) ≪ μ.restrict B :=
    Measure.absolutelyContinuous_of_le_smul ((compression_iff_localized μ _ (hs s) C).mp (hcomp s))
  have hi (s : Time) : Integrable (fun x => h x^2) (π.map (fun γ => γ s)) := by
    let : IsProbabilityMeasure (π.map (fun γ => γ s)) := inferInstance
    refine ⟨(hh.pow_const 2).aestronglyMeasurable, ?_⟩
    exact (((Lp.memLp r).of_measure_le_smul hC (hcomp s)).integrable (by norm_num)
      |>.congr (hν s |>.ae_eq hr)).hasFiniteIntegral
  have hil (s : Time) : Integrable (fun x => Real.log (h x^2+(t:ℝ)^2)) (π.map (fun γ => γ s)) := by
    let : IsProbabilityMeasure (π.map (fun γ => γ s)) := inferInstance
    exact integrable_log_of_lower _ ((hi s).add (integrable_const _)) (sq_pos_of_pos ht)
      (Eventually.of_forall fun x => by nlinarith [sq_nonneg (h x)])
  have hip (s : Time) : Integrable (fun γ : C(Time,X) => Real.log (h (γ s)^2+(t:ℝ)^2)) π :=
    (hil s).comp_measurable (measurable_path_eval s)
  let : IsProbabilityMeasure (π.map (fun γ => γ t)) := inferInstance
  have hg := entropy_regularized_subgradient_localized μ ν₀ (π.map (fun γ => γ t)) hB
    (hmap0 ▸ hνB 0) (hνB t) he0 het (sq_pos_of_pos ht) _ hrn (hmap0 ▸ hil 0) (hil t)
  have he (s : Time) : (∫γ : C(Time,X), Real.log (h (γ s)^2+(t:ℝ)^2) ∂π) =
      ∫x, Real.log (h x^2+(t:ℝ)^2) ∂π.map (fun γ => γ s) :=
    (integral_map (measurable_path_eval s).aemeasurable (hil s).aestronglyMeasurable).symm
  simp only [regularizedPlanLogSecant,planInitialSecant,geodesicExtension_eq]
  rw [integral_sub (hip t) (hip 0),he t,he 0,hmap0]
  apply (div_le_iff₀ ht).mpr
  have heq : ((boltzmannEntropy μ (π.map (fun γ => γ t))-boltzmannEntropy μ ν₀)/(t:ℝ) +
      (t:ℝ)*(μ B).toReal)*(t:ℝ) = boltzmannEntropy μ (π.map (fun γ => γ t))-
        boltzmannEntropy μ ν₀+(t:ℝ)^2*(μ B).toReal := by
    field_simp
  rw [heq]
  linarith only [hg]

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.sqrt_core_raw_entropy_variation
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ t : Time, ∀ᵐ x ∂plan.map (fun γ => γ t), dist x p ≤ R)
    (u ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hh0 : ∀ x, 0 ≤ h x)
    (hi : Integrable h (hausdorff n X))
    (hrep : (SobolevSpace.toLp _ hX.quadratic ρ : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (h0 : plan.map (fun γ => γ 0) = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂plan, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂plan, SobolevSpace.minimalSlope _ hX.quadratic u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (regularizedPlanLogSecant plan h) (𝓝[>] (0:ℝ))
      (𝓝 (-energyForm (hausdorff n X) hX.quadratic u ρ)) ∧
    ∀ᶠ t in 𝓝[>] (0:ℝ), regularizedPlanLogSecant plan h t ≤
      (entropyPlanExtension (hausdorff n X) plan t-
       boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 0)))/t+
       t*((hausdorff n X) (closedBall p R)).toReal := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (closedBall p R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p R).measure_lt_top (μ := μ)⟩
  have hprob (t : Time) : IsProbabilityMeasure (plan.map (fun γ => γ t)) := inferInstance
  let := hprob 0
  have hD : ∀ᵐ γ ∂plan, dist (γ 0) (γ 1) ≤ 2*R := by
    filter_upwards [ae_of_ae_map (measurable_path_eval 0).aemeasurable (hs 0),
      ae_of_ae_map (measurable_path_eval 1).aemeasurable (hs 1)] with γ hγ0 hγ1
    have hh' := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p] at hh'
    linarith
  have hDM : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 plan := by
    apply MemLp.of_bound ((measurable_path_eval 0).dist (measurable_path_eval 1)).aestronglyMeasurable (2*R)
    simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hD
  have hrn : (fun x => h x^2) =ᵐ[μ] fun x => ((plan.map (fun γ => γ 0)).rnDeriv μ x).toReal := by
    rw [h0]
    filter_upwards [Measure.rnDeriv_withDensity μ
      (Lp.stronglyMeasurable (SobolevSpace.toLp _ hX.quadratic ρ)).measurable.ennreal_ofReal,hrep] with x hx hy
    rw [hx,hy,ENNReal.toReal_ofReal (sq_nonneg _)]
  have he (t : Time) : Integrable (fun x => ((plan.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((plan.map (fun γ => γ t)).rnDeriv μ x).toReal) μ := by
    let := hprob t
    exact entropy_integrable_of_bounded_support μ _ ENNReal.ofReal_ne_top (hc t)
      measurableSet_closedBall (hs t)
  refine ⟨sqrt_core_signed_variation μ hX.quadratic plan hg ENNReal.ofReal_ne_top hc hDM
    (by positivity : 0 ≤ 2*R) hD u ρ hh hh0 hi hrep h0 hu had hcontact hb,?_⟩
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,self_mem_nhdsWithin] with t ht ht0
  let t' : Time := ⟨t,ht0.le,ht.le⟩
  have hv := entropy_regularized_raw_plan_secant μ (plan.map (fun γ => γ 0))
    (SobolevSpace.toLp _ hX.quadratic ρ) hh.continuous.measurable hrep hrn (he 0)
    plan rfl ENNReal.ofReal_ne_top hc measurableSet_closedBall hs t' ht0 (he t')
  simpa only [show t = (t':ℝ) from rfl,entropyPlanExtension_eq] using hv

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_plan_dimensional_core_energy
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ t : Time, ∀ᵐ x ∂plan.map (fun γ => γ t), dist x p ≤ R)
    (u₀ u₁ ρ₀ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h₀ h₁ : X → ℝ} {L₀ L₁ : ℝ≥0}
    (hh₀ : LipschitzWith L₀ h₀) (hh₁ : LipschitzWith L₁ h₁)
    (hh₀0 : ∀ x, 0 ≤ h₀ x) (hh₁0 : ∀ x, 0 ≤ h₁ x)
    (hi₀ : Integrable h₀ (hausdorff n X)) (hi₁ : Integrable h₁ (hausdorff n X))
    (hrep₀ : (SobolevSpace.toLp _ hX.quadratic ρ₀ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₀ x^2)
    (hrep₁ : (SobolevSpace.toLp _ hX.quadratic ρ₁ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₁ x^2)
    (h0 : plan.map (fun γ => γ 0) = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (h1 : plan.map (fun γ => γ 1) = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)))
    {φ₀ ψ₀ φ₁ ψ₁ : X → ℝ}
    (hu₀ : φ₀ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u₀)
    (hu₁ : φ₁ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u₁)
    (had₀ : ∀ x y, φ₀ x+ψ₀ y ≤ dist x y^2/2)
    (had₁ : ∀ x y, φ₁ x+ψ₁ y ≤ dist x y^2/2)
    (hcontact₀ : ∀ᵐ γ ∂plan, φ₀ (γ 0)+ψ₀ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hcontact₁ : ∀ᵐ γ ∂plan, φ₁ (γ 1)+ψ₁ (γ 0) = dist (γ 0) (γ 1)^2/2)
    (hb₀ : ∀ᵐ γ ∂plan, SobolevSpace.minimalSlope _ hX.quadratic u₀ (γ 0) ≤ dist (γ 0) (γ 1))
    (hb₁ : ∀ᵐ γ ∂plan, SobolevSpace.minimalSlope _ hX.quadratic u₁ (γ 1) ≤ dist (γ 0) (γ 1))
    (N : ℝ) (hN : (n:ℝ) ≤ N) :
    K*(wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal+
      (boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 1))-
       boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 0)))^2/N ≤
    energyForm (hausdorff n X) hX.quadratic u₀ ρ₀+
      energyForm (hausdorff n X) hX.quadratic u₁ ρ₁
 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let rev := plan.map reversePath
  let : IsProbabilityMeasure rev := inferInstance
  have hrcomp (s : Time) : rev.map (fun γ => γ s) ≤ ENNReal.ofReal C • μ := by
    rw [reversePlan_eval]
    exact hc _
  have hrS (s : Time) : ∀ᵐ x ∂rev.map (fun γ => γ s), dist x p ≤ R := by
    rw [reversePlan_eval]
    exact hs _
  have hrevEmb : MeasurableEmbedding (reversePath (X := X)) :=
    (MeasurableEquiv.ofInvolutive reversePath reversePath_reversePath measurable_reversePath).measurableEmbedding
  have hrg : ∀ᵐ γ ∂rev, IsGeodesic γ := by
    apply hrevEmb.ae_map_iff.mpr
    exact hg.mono fun γ hγ => isGeodesic_reversePath γ hγ
  have hr0 : rev.map (fun γ => γ 0) = μ.withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)) := by
    change (plan.map reversePath).map (fun γ => γ 0) = _
    rw [reversePlan_eval,reverseTime_zero]
    exact h1
  have hrcontact : ∀ᵐ γ ∂rev, φ₁ (γ 0)+ψ₁ (γ 1) = dist (γ 0) (γ 1)^2/2 := by
    apply hrevEmb.ae_map_iff.mpr
    exact hcontact₁.mono fun γ hγ => by
      simpa only [reversePath_apply,reverseTime_zero,reverseTime_one,dist_comm] using hγ
  have hrb : ∀ᵐ γ ∂rev, SobolevSpace.minimalSlope _ hX.quadratic u₁ (γ 0) ≤ dist (γ 0) (γ 1) := by
    apply hrevEmb.ae_map_iff.mpr
    exact hb₁.mono fun γ hγ => by simpa only [reversePath_apply,reverseTime_zero,reverseTime_one,dist_comm] using hγ
  obtain ⟨hA,hAb⟩ := hX.sqrt_core_raw_entropy_variation K n hn plan hg C hc p hR hs
    u₀ ρ₀ hh₀ hh₀0 hi₀ hrep₀ h0 hu₀ had₀ hcontact₀ hb₀
  obtain ⟨hB,hBb⟩ := hX.sqrt_core_raw_entropy_variation K n hn rev hrg C hrcomp p hR hrS
    u₁ ρ₁ hh₁ hh₁0 hi₁ hrep₁ hr0 hu₁ had₁ hrcontact hrb
  have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      regularizedPlanLogSecant plan h₀ t ≤
        (entropyPlanExtension μ plan t-boltzmannEntropy μ (plan.map (fun γ => γ 0)))/t+
          t*(μ (closedBall p R)).toReal ∧
      regularizedPlanLogSecant rev h₁ t ≤
        (entropyPlanExtension μ plan (1-t)-boltzmannEntropy μ (plan.map (fun γ => γ 1)))/t+
          t*(μ (closedBall p R)).toReal := by
    have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    filter_upwards [hAb,hBb,hsmall,self_mem_nhdsWithin] with t htA htB ht1 ht0
    refine ⟨htA,?_⟩
    let t' : Time := ⟨t,ht0.le,ht1.le⟩
    have he : entropyPlanExtension μ rev t = entropyPlanExtension μ plan (1-t) := by
      change entropyPlanExtension μ rev (t':ℝ) = entropyPlanExtension μ plan ((reverseTime t'):ℝ)
      rw [entropyPlanExtension_eq,entropyPlanExtension_eq,reversePlan_eval]
    rwa [he,reversePlan_eval,reverseTime_zero] at htB
  have hfinal := hX.compressed_plan_dimensional_endpoint K n hn plan hg hp C hc p hR hs N hN
    (regularizedPlanLogSecant plan h₀) (regularizedPlanLogSecant rev h₁) hA hB hbound
  simpa only [neg_neg,sub_neg_eq_add] using hfinal


end RegularPointCoordinates

end OAI
