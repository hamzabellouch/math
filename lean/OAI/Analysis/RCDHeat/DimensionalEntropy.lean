import Mathlib
import OAI.Analysis.RCDHeat.RestrictedDensity

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: DimensionalEntropy, DimensionalEntropySubsegment, EntropyEndpoints, DiscreteDimensionalEntropy, MidpointGrid, LogCoshLimit. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_plan_dimensional_entropy_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X) (N : ℝ) (hN : (n : ℝ) ≤ N) :
    boltzmannEntropy (hausdorff n X)
        (plan.map (fun γ => γ (⟨1/2, by norm_num, by norm_num⟩ : Time))) ≤
      (boltzmannEntropy (hausdorff n X) ν₀ + boltzmannEntropy (hausdorff n X) ν₁)/2 -
      (K/8)*(wassersteinSq ν₀ ν₁).toReal - N*Real.log (Real.cosh
        ((boltzmannEntropy (hausdorff n X) ν₀ - boltzmannEntropy (hausdorff n X) ν₁)/(2*N)))
 := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (closedBall p (3*R))) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p (3*R)).measure_lt_top (μ := μ)⟩
  let ν := fun s : Time => plan.map (fun γ => γ s)
  have hprob (s : Time) : IsProbabilityMeasure (ν s) := inferInstance
  have hac (s : Time) : ν s ≪ μ := Measure.absolutelyContinuous_of_le_smul (hc s)
  have he := optimalPlan_endpoints ν₀ ν₁ plan hp
  have hs (s : Time) : ∀ᵐ x ∂ν s, x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ plan hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 s
  have hlog (s : Time) : Integrable (fun x => Real.log ((ν s).rnDeriv μ x).toReal) (ν s) := by
    let := hprob s
    exact (integrable_toReal_rnDeriv_mul_iff (hac s)).mp
      (entropy_integrable_of_bounded_support μ (ν s) ENNReal.ofReal_ne_top (hc s)
        measurableSet_closedBall (hs s))
  let L := fun (s : Time) (γ : C(Time,X)) => Real.log ((ν s).rnDeriv μ (γ s)).toReal
  have hLI (s : Time) : Integrable (L s) plan := (hlog s).comp_measurable (measurable_path_eval s)
  have hEI (s : Time) : (∫ γ, L s γ ∂plan) = boltzmannEntropy μ (ν s) := by
    rw [←integral_map (measurable_path_eval s).aemeasurable (hlog s).aestronglyMeasurable]
    let := hprob s
    exact (integral_rnDeriv_smul (f := fun x => Real.log ((ν s).rnDeriv μ x).toReal) (hac s)).symm
  have hRN (s : Time) : ∀ᵐ γ ∂plan, (ν s).rnDeriv μ (γ s) ≠ 0 ∧ (ν s).rnDeriv μ (γ s) ≠ ∞ := by
    let := hprob s
    have hh : ∀ᵐ x ∂ν s, (ν s).rnDeriv μ x ≠ 0 ∧ (ν s).rnDeriv μ x ≠ ∞ := by
      filter_upwards [Measure.rnDeriv_pos (hac s),(hac s).ae_le (Measure.rnDeriv_lt_top (ν s) μ)] with x hx hy
      exact ⟨hx.ne',hy.ne⟩
    exact ae_of_ae_map (measurable_path_eval s).aemeasurable hh
  let m : Time := ⟨1/2,by norm_num,by norm_num⟩
  have hN' : 1 < N := lt_of_lt_of_le (by exact_mod_cast (show 1 < n by omega)) hN
  have hpt := hX.compressed_plan_pointwise_fullCD K n hn ν₀ ν₁ p hR hs0 hs1 plan hg hp C hc N hN m
  rw [←he.1,←he.2] at hpt
  have hpoint : ∀ᵐ γ ∂plan, L m γ ≤ (L 0 γ+L 1 γ)/2-(K/8)*dist (γ 0) (γ 1)^2-
      N*Real.log (Real.cosh ((L 0 γ-L 1 γ)/(2*N))) := by
    filter_upwards [hpt,hRN 0,hRN 1,hRN m] with γ hγ h0 h1 hm
    have hcd : tau K N (1/2) (dist (γ 0) (γ 1))*((ν 0).rnDeriv μ (γ 0))^(-(1/N))+
        tau K N (1/2) (dist (γ 0) (γ 1))*((ν 1).rnDeriv μ (γ 1))^(-(1/N)) ≤
          ((ν m).rnDeriv μ (γ m))^(-(1/N)) := by
      simpa only [m,show 1-(1/2:ℝ) = 1/2 by norm_num] using hγ
    have hh := density_dimensional_log_midpoint K N _ hN' dist_nonneg _ _ _
      h0.1 h0.2 h1.1 h1.2 hm.1 hm.2 hcd
    convert hh using 1
    dsimp only [L]
    ring
  have hd := optimalPlan_dist_sq_integrable ν₀ ν₁ plan hp p
    (integrable_dist_sq_of_ae_bounded ν₀ p hs0) (integrable_dist_sq_of_ae_bounded ν₁ p hs1)
  have hcost : (wassersteinSq ν₀ ν₁).toReal = ∫ γ, dist (γ 0) (γ 1)^2 ∂plan := by
    rw [wassersteinSq_eq_cost hp,transportCost_plan_eq_integral plan hd,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hi := dimensional_log_midpoint_integral plan (L 0) (L 1) (L m)
    (fun γ => (K/8)*dist (γ 0) (γ 1)^2) (hLI 0) (hLI 1) (hLI m) (hd.const_mul (K/8))
    (zero_lt_one.trans hN') hpoint
  rw [hEI 0,hEI 1,hEI m,integral_const_mul,←hcost] at hi
  simpa only [ν,he.1,he.2,m] using hi


 
theorem NoncollapsedRCD.compressed_plan_dimensional_entropy_submidpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ s : Time,
      plan.map (fun γ => γ s) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ s : Time, ∀ᵐ x ∂plan.map (fun γ => γ s), dist x p ≤ R)
    (N : ℝ) (hN : (n:ℝ) ≤ N) (a b : Time) :
    boltzmannEntropy (hausdorff n X)
        (plan.map (fun γ => γ (timeSegment a b midpointTime))) ≤
      (boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ a))+
       boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ b)))/2-
      (K/8)*((a:ℝ)-(b:ℝ))^2*
        (wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal-
      N*Real.log (Real.cosh ((boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ a))-
        boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ b)))/(2*N))) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : Nonempty X := ⟨p⟩
  have hprob (s : Time) : IsProbabilityMeasure (plan.map (fun γ => γ s)) := inferInstance
  let := hprob a
  let := hprob b
  let := hprob 0
  let := hprob 1
  have hfin : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [←wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le _ p (hs 0))
      (finiteSecondMoment_of_ae_dist_le _ p (hs 1))
  obtain ⟨hprob',hg',hp'⟩ := geodesic_subpath_law plan hg hp hfin a b
  let := hprob'
  have hcomp (s : Time) : (plan.map (subpath a b)).map (fun γ => γ s) ≤
      ENNReal.ofReal C • hausdorff n X := by
    rw [subpath_map_eval]
    exact hc _
  have he : (wassersteinSq (plan.map (fun γ => γ a)) (plan.map (fun γ => γ b))).toReal =
      ((a:ℝ)-(b:ℝ))^2 *
        (wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal := by
    rw [wassersteinSq_eq_cost (geodesic_plan_optimal_marginals plan hg hp hfin a b),
      geodesic_plan_cost plan hg, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),sq_abs, wassersteinSq_eq_cost hp]
  have hh := hX.compressed_plan_dimensional_entropy_midpoint K n hn _ _ p hR (hs a) (hs b)
    (plan.map (subpath a b)) hg' hp' C hcomp N hN
  rw [subpath_map_eval,he] at hh
  convert hh using 1
  ring


 
lemma NoncollapsedRCD.entropy_compressed_plan_continuousAt_one
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ t : Time, ∀ᵐ x ∂plan.map (fun γ => γ t), dist x p ≤ R) :
    ContinuousAt (fun t : Time => boltzmannEntropy (hausdorff n X)
      (plan.map (fun γ => γ t))) 1 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let E := fun t : Time => boltzmannEntropy μ (plan.map (fun γ => γ t))
  let q := (K/2)*(wassersteinSq (plan.map (fun γ => γ 0))
     (plan.map (fun γ => γ 1))).toReal
  let G := fun t : Time => (1-(t:ℝ))*E 0+(t:ℝ)*E 1-q*(t:ℝ)*(1-(t:ℝ))
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hG1 : G 1 = E 1 := by simp [G]
  have hbound (t : Time) : E t ≤ G t := by
    let : IsProbabilityMeasure (plan.map (fun γ => γ 0)) := inferInstance
    let : IsProbabilityMeasure (plan.map (fun γ => γ 1)) := inferInstance
    have hh := hX.entropy_convexity_bounded_plan_marginal K n hn _ _ C
      (hc 0) (hc 1) p hR (hs 0) (hs 1) plan hg hp t (hc t)
    convert hh using 1
    dsimp [G,E,q,μ]
    ring
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨lowerSemicontinuous_entropy_compressed_plan μ plan C hc p R hs 1,?_⟩
  intro b hb
  have hh := (hG.continuousAt (x := (1 : Time))).upperSemicontinuousAt b (by simpa only [hG1] using hb)
  exact hh.mono fun t ht => (hbound t).trans_lt ht

end

 
section

 

open Set Filter
open scoped BigOperators Topology

lemma sum_second_difference (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, (f i+f (i+2)-2*f (i+1))) =
      f 0-f 1+f (m+1)-f m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ,hm]
    ring

lemma sum_centered_difference (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, (f (i+2)-f i)) =
      f (m+1)+f m-f 1-f 0 := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ,hm]
    ring

lemma sum_log_cosh_ge (f : ℕ → ℝ) (m : ℕ) (hm : 0 < m) :
    (m:ℝ)*Real.log (Real.cosh ((∑ i ∈ Finset.range m, f i)/(m:ℝ))) ≤
      ∑ i ∈ Finset.range m, Real.log (Real.cosh (f i)) := by
  let ξ := (∑ i ∈ Finset.range m, f i)/(m:ℝ)
  have hh := Finset.sum_le_sum (s := Finset.range m) (fun i _ => log_cosh_tangent ξ (f i))
  have hsum : (∑ i ∈ Finset.range m, (f i-ξ)) = 0 := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    dsimp only [ξ]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hm.ne' : (m:ℝ) ≠ 0),sub_self]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ←Finset.mul_sum,hsum,mul_zero,add_zero] at hh
  exact hh

lemma dimensional_midpoint_discrete_sum (f : ℕ → ℝ) {N κ : ℝ} (hN : 0 < N)
    (m : ℕ) (hm : 0 < m)
    (hmid : ∀ i < m, f (i+1) ≤ (f i+f (i+2))/2-κ/2-
      N*Real.log (Real.cosh ((f i-f (i+2))/(2*N)))) :
    (m:ℝ)*κ+2*N*(m:ℝ)*Real.log (Real.cosh
      ((f (m+1)+f m-f 1-f 0)/(2*N*(m:ℝ)))) ≤ f 0-f 1+f (m+1)-f m := by
  have hh : ∀ i ∈ Finset.range m,
      κ+2*N*Real.log (Real.cosh ((f (i+2)-f i)/(2*N))) ≤
        f i+f (i+2)-2*f (i+1) := by
    intro i hi
    have h := hmid i (Finset.mem_range.mp hi)
    rw [show (f i-f (i+2))/(2*N) = -((f (i+2)-f i)/(2*N)) by ring,Real.cosh_neg] at h
    linarith
  have hs := Finset.sum_le_sum hh
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ←Finset.mul_sum,sum_second_difference] at hs
  have hj := sum_log_cosh_ge (fun i => (f (i+2)-f i)/(2*N)) m hm
  have he : (∑ i ∈ Finset.range m, (f (i+2)-f i)/(2*N))/(m:ℝ) =
      (f (m+1)+f m-f 1-f 0)/(2*N*(m:ℝ)) := by
    rw [←Finset.sum_div,sum_centered_difference]
    ring
  rw [he] at hj
  have hmul := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ 2*N)
  nlinarith only [hs,hmul]

end

 
section

 
open Set Filter
open scoped Topology

lemma dimensional_midpoint_grid (E : ℝ → ℝ) {N κ : ℝ} (hN : 0 < N)
    (hmid : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      E ((x+y)/2) ≤ (E x+E y)/2-κ*(x-y)^2/8-
        N*Real.log (Real.cosh ((E x-E y)/(2*N))))
    (m : ℕ) (hm : 0 < m) :
    κ*(m:ℝ)/((m:ℝ)+1) + 2*N*(m:ℝ)*((m:ℝ)+1)*Real.log (Real.cosh
      ((E 1+E (1-1/((m:ℝ)+1))-E (1/((m:ℝ)+1))-E 0)/(2*N*(m:ℝ)))) ≤
      (E 0-E (1/((m:ℝ)+1))+E 1-E (1-1/((m:ℝ)+1)))*((m:ℝ)+1) := by
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hD : 0 < (m:ℝ)+1 := by positivity
  let f : ℕ → ℝ := fun i => E ((i:ℝ)/((m:ℝ)+1))
  have hc : ∀ i < m, f (i+1) ≤ (f i+f (i+2))/2-(κ/((m:ℝ)+1)^2)/2-
      N*Real.log (Real.cosh ((f i-f (i+2))/(2*N))) := by
    intro i hi
    have hiR : (i:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hi
    have h0 : (i:ℝ)/((m:ℝ)+1) ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity,(div_le_one hD).mpr (by linarith)⟩
    have h2 : ((i:ℝ)+2)/((m:ℝ)+1) ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity,(div_le_one hD).mpr (by linarith)⟩
    have hh := hmid _ h0 _ h2
    have he : ((i:ℝ)/((m:ℝ)+1)+((i:ℝ)+2)/((m:ℝ)+1))/2 =
        ((i:ℝ)+1)/((m:ℝ)+1) := by ring
    have hk : κ*((i:ℝ)/((m:ℝ)+1)-((i:ℝ)+2)/((m:ℝ)+1))^2/8 =
        (κ/((m:ℝ)+1)^2)/2 := by
      field_simp
      ring
    rw [he,hk] at hh
    simpa only [f,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh
  have hh := dimensional_midpoint_discrete_sum f hN m hm hc
  have hf0 : f 0 = E 0 := by simp [f]
  have hf1 : f 1 = E (1/((m:ℝ)+1)) := by simp [f]
  have hfm : f m = E (1-1/((m:ℝ)+1)) := by
    dsimp only [f]
    congr 1
    field_simp
    ring
  have hfm1 : f (m+1) = E 1 := by simp [f,hD.ne']
  rw [hf0,hf1,hfm,hfm1] at hh
  have hh' := mul_le_mul_of_nonneg_right hh hD.le
  convert hh' using 1
  first | rfl | field_simp

end

 

 

open Set Filter
open scoped Topology

lemma tendsto_log_cosh_div_sq :
    Tendsto (fun x : ℝ => Real.log (Real.cosh x)/x^2) (𝓝[≠] (0:ℝ)) (𝓝 (1/2:ℝ)) := by
  have h1 : Tendsto (fun x : ℝ => (Real.sinh x/Real.cosh x)/x) (𝓝[≠] (0:ℝ)) (𝓝 (1:ℝ)) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using (hasDerivAt_sinh_div_cosh 0).tendsto_slope_zero
  have hdg (x : ℝ) : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  apply HasDerivAt.lhopital_zero_nhdsNE
    (Eventually.of_forall hasDerivAt_log_cosh) (Eventually.of_forall hdg)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (show x ≠ 0 from hx)
  · simpa using ((Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne')).tendsto 0).mono_left nhdsWithin_le_nhds
  · simpa only [Pi.pow_apply,id_eq,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      ((show Continuous (fun y : ℝ => y^2) from continuous_id.pow 2).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  · convert h1.div_const 2 using 1
    funext x
    ring

noncomputable def logCoshRatio (x : ℝ) : ℝ := if x = 0 then 1/2 else Real.log (Real.cosh x)/x^2

lemma continuousAt_logCoshRatio_zero : ContinuousAt logCoshRatio 0 := by
  change Tendsto logCoshRatio (𝓝 (0:ℝ)) (𝓝 (logCoshRatio 0))
  rw [←nhdsNE_sup_pure,tendsto_sup]
  constructor
  · have hh : logCoshRatio =ᶠ[𝓝[≠] (0:ℝ)] (fun x => Real.log (Real.cosh x)/x^2) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [logCoshRatio,ite_eq_right (show x ≠ 0 from hx)]
    simpa [logCoshRatio] using (tendsto_log_cosh_div_sq.congr' hh.symm)
  · exact tendsto_pure_nhds _ _

lemma log_cosh_eq_sq_mul_ratio (x : ℝ) : Real.log (Real.cosh x) = x^2*logCoshRatio x := by
  by_cases hx : x = 0
  · simp [hx,logCoshRatio]
  · simp only [logCoshRatio,ite_eq_right hx]
    field_simp

lemma dimensional_log_cosh_scaled_limit {α : Type*} {l : Filter α}
    (a b : α → ℝ) {a₀ : ℝ} (ha : Tendsto a l (𝓝 a₀))
    (hb : Tendsto b l (𝓝 (0:ℝ))) (N : ℝ) (hN : N ≠ 0) :
    Tendsto (fun i => 2*N*(a i)^2/(4*N^2)*logCoshRatio (a i*b i/(2*N)))
      l (𝓝 (a₀^2/(4*N))) := by
  have ht : Tendsto (fun i => a i*b i/(2*N)) l (𝓝 (0:ℝ)) := by
    simpa using (ha.mul hb).div_const (2*N)
  have hh := (((tendsto_const_nhds (x := 2*N)).mul (ha.pow 2)).div_const (4*N^2)).mul
    (continuousAt_logCoshRatio_zero.tendsto.comp ht)
  have hzero : logCoshRatio 0 = (1/2:ℝ) := by simp [logCoshRatio]
  rw [hzero] at hh
  have he : 2*N*a₀^2/(4*N^2)*(1/2) = a₀^2/(4*N) := by
    field_simp [hN]
  rw [he] at hh
  exact hh


end RegularPointCoordinates

end OAI
