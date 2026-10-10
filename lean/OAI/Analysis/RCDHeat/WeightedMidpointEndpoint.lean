import Mathlib
import OAI.Analysis.RCDHeat.DimensionalH1

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedMidpointEndpoint, WeightedPlanEntropyEndpoint, WeightedDimensionalCore, WeightedDimensionalCoreDual, WeightedDimensionalDualLimit. -/



namespace RegularPointCoordinates

section

 

open Set Filter
open scoped Topology

theorem weighted_dimensional_midpoint_endpoint (E A B : ℝ → ℝ) {N κ M α β : ℝ}
    (hN : 0 < N)
    (hmid : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      E ((x+y)/2) ≤ (E x+E y)/2-κ*(x-y)^2/8-
        N*Real.log (Real.cosh ((E x-E y)/(2*N))))
    (hA : Tendsto A (𝓝[>] (0:ℝ)) (𝓝 α))
    (hB : Tendsto B (𝓝[>] (0:ℝ)) (𝓝 β))
    (hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      A t ≤ (E t-E 0)/t+t*M ∧ B t ≤ (E (1-t)-E 1)/t+t*M)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    κ*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤ -a^2*α-b^2*β := by
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
  let g : ℕ → ℝ := fun k => κ*(1-t k)*(a^2+a*b+b^2)/3+
    κ*t k*δ k*(a-b)^2/6-N*(a-b)^2*(1+δ k)
  have hg : Tendsto g atTop (𝓝 (κ*(a^2+a*b+b^2)/3-N*(a-b)^2)) := by
    have h1 := (((tendsto_const_nhds (x := (1:ℝ))).sub ht).const_mul κ).mul_const
      (a^2+a*b+b^2) |>.div_const 3
    have h2 := (((ht.const_mul κ).mul hδ).mul_const ((a-b)^2)).div_const 6
    have h3 := (((tendsto_const_nhds (x := (1:ℝ))).add hδ).const_mul (N*(a-b)^2))
    simpa only [sub_zero,mul_one,mul_zero,zero_mul,zero_div,add_zero] using (h1.add h2).sub h3
  have hright : Tendsto (fun k => -a^2*A (t k)-b^2*B (t k)+(a^2+b^2)*t k*M)
      atTop (𝓝 (-a^2*α-b^2*β)) := by
    simpa using (((hA.comp ht').const_mul (-a^2)).sub
      ((hB.comp ht').const_mul (b^2))).add ((ht.const_mul (a^2+b^2)).mul_const M)
  apply le_of_tendsto_of_tendsto hg hright
  filter_upwards [ht'.eventually hbound] with k hk
  have hgrid := weighted_dimensional_midpoint_grid E hN hmid a b ha hb (k+1) (by omega)
  have hk1 : (k:ℝ)+1 ≠ 0 := by positivity
  have hk2 : (k:ℝ)+2 ≠ 0 := by positivity
  have hegrid : g k ≤ (a^2*(E 0-E (t k))+b^2*(E 1-E (1-t k)))/t k := by
    convert hgrid using 1 <;>
      dsimp only [g,t,δ] <;> push_cast <;> field_simp <;> ring_nf
  apply hegrid.trans
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hk.1 (sq_nonneg a))
    (mul_le_mul_of_nonneg_left hk.2 (sq_nonneg b))
  have he : (a^2*(E 0-E (t k))+b^2*(E 1-E (1-t k)))/t k =
      -(a^2*((E (t k)-E 0)/t k)+b^2*((E (1-t k)-E 1)/t k)) := by ring
  rw [he]
  nlinarith only [hsum]

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_plan_weighted_dimensional_endpoint
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
        boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ 1)))/t+t*M) (c d : ℝ) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) :
    K*(wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal*
      (c^2+c*d+d^2)/3-N*(c-d)^2 ≤ -c^2*a-d^2*b := by
  let μ := hausdorff n X
  let E := entropyPlanExtension μ plan
  have he (t : Time) : E t = boltzmannEntropy μ (plan.map (fun γ => γ t)) :=
    entropyPlanExtension_eq μ plan t
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
  have hh := weighted_dimensional_midpoint_endpoint E A B hNpos hmid hA hB hbnd c d hc0 hd0
  simpa only [show (0:ℝ) = ((0:Time):ℝ) from rfl,show (1:ℝ) = ((1:Time):ℝ) from rfl,he] using hh


 
theorem NoncollapsedRCD.compressed_plan_weighted_dimensional_core_energy
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
    (N : ℝ) (hN : (n:ℝ) ≤ N) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    K*(wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal*
      (a^2+a*b+b^2)/3-N*(a-b)^2 ≤
    a^2*energyForm (hausdorff n X) hX.quadratic u₀ ρ₀+
      b^2*energyForm (hausdorff n X) hX.quadratic u₁ ρ₁
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
  have hfinal := hX.compressed_plan_weighted_dimensional_endpoint K n hn plan hg hp C hc p hR hs N hN
    (regularizedPlanLogSecant plan h₀) (regularizedPlanLogSecant rev h₁) hA hB hbound a b ha hb
  convert hfinal using 1
  ring


 
theorem NoncollapsedRCD.weighted_dimensional_core_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ₀ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h₀ h₁ : X → ℝ} {L₀ L₁ : ℝ≥0}
    (hh₀ : LipschitzWith L₀ h₀) (hh₁ : LipschitzWith L₁ h₁)
    (hh₀0 : ∀ x, 0 ≤ h₀ x) (hh₁0 : ∀ x, 0 ≤ h₁ x)
    (hi₀ : Integrable h₀ (hausdorff n X)) (hi₁ : Integrable h₁ (hausdorff n X))
    (hrep₀ : (SobolevSpace.toLp _ hX.quadratic ρ₀ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₀ x^2)
    (hrep₁ : (SobolevSpace.toLp _ hX.quadratic ρ₁ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₁ x^2)
    (hν₀ : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (hν₁ : ν₁ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)))
    (N : ℝ) (hN : (n:ℝ) ≤ N) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁
      p (16*R) (10*R^2) ⟨5*R,by positivity⟩,
      K*(wassersteinSq ν₀ ν₁).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤
        a^2*energyForm (hausdorff n X) hX.quadratic d.u ρ₀+
          b^2*energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  obtain ⟨u,v,φ,ψ,hφ,hψ,hφb,hψb,hφS,hψS,hφc,hψc,hu,hv,had,hcontact,hb₀,hb₁⟩ :=
    hp.bidirectional_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) (Measure.absolutelyContinuous_of_le_smul h1)
      p hR hs0 hs1
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hcontact' := ae_of_ae_map hm.aemeasurable hcontact
  have hb₀' := ae_of_ae_map hm.aemeasurable hb₀
  have hb₁' := ae_of_ae_map hm.aemeasurable hb₁
  let D := (compressionBudget K n (2*R) C).toNNReal
  have hD : ENNReal.ofReal (D:ℝ) = compressionBudget K n (2*R) C := by
    rw [ENNReal.ofReal_coe_nnreal,ENNReal.coe_toNNReal (compressionBudget_ne_top K n (2*R) hC)]
  have hc (t : Time) : π.map (fun γ => γ t) ≤ ENNReal.ofReal (D:ℝ) • μ := by
    rw [hD]; exact (hall t).1
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), dist x p ≤ 3*R := by
    apply ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall |>.mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hpaired := hX.compressed_plan_weighted_dimensional_core_energy (φ₀ := φ) (ψ₀ := ψ) (φ₁ := ψ) (ψ₁ := φ) K n hn π hg
    (by rwa [he.1,he.2]) D hc p (by positivity : 0 ≤ 3*R) hs
    u v ρ₀ ρ₁ hh₀ hh₁ hh₀0 hh₁0 hi₀ hi₁ hrep₀ hrep₁
    (he.1.trans hν₀) (he.2.trans hν₁) hu hv had
    (fun x y => by simpa only [add_comm,dist_comm] using had y x)
    hcontact' (hcontact'.mono fun γ hγ => by simpa only [add_comm] using hγ)
    hb₀' hb₁' N hN a b ha hb
  let d : CompactSobolevDual μ hX.quadratic ν₀ ν₁ p (16*R) (10*R^2) ⟨5*R,by positivity⟩ :=
    ⟨u,v,φ,ψ,hφ,hψ,hφb,hψb,hφS,hψS,hφc,hψc,hu,hv,had,
      optimal_plan_dual_eq hp hdi (hφ.continuous.integrable_of_hasCompactSupport hφc)
        (hψ.continuous.integrable_of_hasCompactSupport hψc) hcontact'⟩
  refine ⟨d,?_⟩
  simpa only [he.1,he.2] using hpaired

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.weighted_dimensional_dual_limit
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) (νs : ℕ → Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] [∀ i, IsProbabilityMeasure (νs i)]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (hcs : ∀ i, νs i ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (hss : ∀ i, ∀ᵐ x ∂νs i, dist x p ≤ R)
    {fs : ℕ → X → ℝ} {M : ℝ}
    (hfm : ∀ i, Measurable (fs i)) (hfn : ∀ i x, 0 ≤ fs i x ∧ fs i x ≤ M)
    (hfs : ∀ i x, fs i x ≠ 0 → x ∈ closedBall p R)
    (ρ₀ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    (qs : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hq : Tendsto qs atTop (𝓝 ρ₀))
    (hρ₀ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ₀ x)
    (hfl : ∀ᵐ x ∂hausdorff n X, Tendsto (fun i => fs i x) atTop
      (𝓝 (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (hd : ∀ i, νs i = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (fs i x)))
    (hd0 : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (hEnt : Tendsto (fun i => boltzmannEntropy (hausdorff n X) (νs i)) atTop
      (𝓝 (boltzmannEntropy (hausdorff n X) ν₀)))
    {S A : ℝ} {L : ℝ≥0}
    (ds : ∀ i, CompactSobolevDual (hausdorff n X) hX.quadratic (νs i) ν₁ p S A L)
    (N a b : ℝ)
    (henergy : ∀ i, K*(wassersteinSq (νs i) ν₁).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤
      a^2*energyForm (hausdorff n X) hX.quadratic (ds i).u (qs i)+
        b^2*energyForm (hausdorff n X) hX.quadratic (ds i).v ρ₁) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁ p S A L,
      K*(wassersteinSq ν₀ ν₁).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤
        a^2*energyForm (hausdorff n X) hX.quadratic d.u ρ₀+
          b^2*energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨u,φ,ψ,s,hsm,hφ,hψ,hφB,hψB,hφS,hψS,hu,hφlim,hψlim,hub,hul⟩ :=
    SobolevSpace.common_support_dual_subsequence μ hX.quadratic p S A L
      (fun i => (ds i).u) (fun i => (ds i).φ) (fun i => (ds i).ψ)
      (fun i => (ds i).lipφ) (fun i => (ds i).lipψ)
      (fun i => (ds i).boundφ) (fun i => (ds i).boundψ)
      (fun i => (ds i).supportφ) (fun i => (ds i).supportψ) (fun i => (ds i).repu)
  have hφc : HasCompactSupport φ := (isCompact_closedBall p S).of_isClosed_subset (isClosed_tsupport φ) hφS
  have hψc : HasCompactSupport ψ := (isCompact_closedBall p S).of_isClosed_subset (isClosed_tsupport ψ) hψS
  let v := SobolevSpace.ofLipschitzCompact μ hX.quadratic hψ hψc
  have hv : ψ =ᵐ[μ] SobolevSpace.toLp μ hX.quadratic v :=
    (SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hψ hψc).symm
  have hvb (i : ℕ) : ‖(ds (s i)).v‖ ≤ Real.sqrt ((A^2+(L:ℝ)^2)*(μ (closedBall p S)).toReal) :=
    SobolevSpace.norm_le_of_common_support μ hX.quadratic p S A L _
      (ds (s i)).lipψ (ds (s i)).boundψ (ds (s i)).supportψ (ds (s i)).repv
  have hvl : Tendsto (fun i => SobolevSpace.toLp μ hX.quadratic (ds (s i)).v) atTop
      (𝓝 (SobolevSpace.toLp μ hX.quadratic v)) :=
    SobolevSpace.toLp_tendsto_of_common_support μ hX.quadratic p S A L
      (fun i => (ds (s i)).lipψ) hψ (fun i => (ds (s i)).boundψ) hψB
      (fun i => (ds (s i)).supportψ) hψS (fun i => (ds (s i)).repv) hv hψlim
  have had (x y : X) : φ x+ψ y ≤ dist x y^2/2 :=
    le_of_tendsto ((hφlim x).add (hψlim y)) (Eventually.of_forall fun i => (ds (s i)).admissible x y)
  have hcost := hX.bounded_density_dual_limit K n hn ν₀ ν₁ (fun i => νs (s i)) hC h0 h1
    (fun i => hcs (s i)) p hR hs0 hs1 (fun i => hss (s i))
    (fun i => hfm (s i)) (fun i => hfn (s i)) (fun i => hfs (s i))
    (Lp.stronglyMeasurable (SobolevSpace.toLp μ hX.quadratic ρ₀)).measurable hρ₀
    (hfl.mono fun x hx => hx.comp hsm.tendsto_atTop) (fun i => hd (s i)) hd0
    (fun i => (ds (s i)).lipφ) (fun i => (ds (s i)).lipψ)
    (fun i => (ds (s i)).boundφ) (fun i => (ds (s i)).boundψ)
    hφ hψ hφB hψB hφlim hψlim had (fun i => (ds (s i)).dual)
  let d : CompactSobolevDual μ hX.quadratic ν₀ ν₁ p S A L :=
    ⟨u,v,φ,ψ,hφ,hψ,hφB,hψB,hφS,hψS,hφc,hψc,hu,hv,had,hcost.2⟩
  have hE0 := SobolevSpace.energyForm_tendsto_weak_strong μ hX.quadratic hub hul
    (hq.comp hsm.tendsto_atTop)
  have hE1 := SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded μ hX.quadratic hvb hvl ρ₁
  have hEntSubseq := hEnt.comp hsm.tendsto_atTop
  refine ⟨d,?_⟩
  apply (add_le_add_iff_right (boltzmannEntropy μ ν₀)).mp
  exact le_of_tendsto_of_tendsto (((((hcost.1.const_mul K).mul_const
      (a^2+a*b+b^2)).div_const 3).sub_const (N*(a-b)^2)).add hEntSubseq)
    (((hE0.const_mul (a^2)).add (hE1.const_mul (b^2))).add hEntSubseq)
    (Eventually.of_forall fun index => add_le_add (henergy (s index)) le_rfl)


end RegularPointCoordinates

end OAI
