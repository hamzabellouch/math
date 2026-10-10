import Mathlib
import OAI.Analysis.RCDHeat.CrossingOptimal
import OAI.Analysis.RCDHeat.EntropySubsegment

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: Noncrossing, ConditionalPair, ConditionalSets, InteriorSingularity, EntropyEndpoint, EntropyEndpointFork. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem NoncollapsedRCD.compressed_optimal_plan_no_interior_crossing
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hcomp : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (σ : Measure (C(Time,X) × C(Time,X))) [IsProbabilityMeasure σ]
    (hσ0 : σ.map Prod.fst = plan) (hσ1 : σ.map Prod.snd = plan)
    (a : Time) (ha : 0 < (a:ℝ)) (ha1 : (a:ℝ) < 1)
    (hagree : ∀ᵐ z ∂σ, z.1 a = z.2 a) :
    ∀ᵐ z ∂σ, z.1 = z.2
 := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  have hfuture := hX.crossing_paths_agree_future K n hn ν₀ ν₁ p hR hs0 hs1
    plan hg hp C hcomp σ hσ0 hσ1 a ha ha1 hagree
  let P := plan.map reversePath
  let : IsProbabilityMeasure P := inferInstance
  have hPg : ∀ᵐ γ ∂P, IsGeodesic γ := by
    apply (ae_map_iff measurable_reversePath.aemeasurable isClosed_geodesicSet.measurableSet).mpr
    exact hg.mono fun γ hz => isGeodesic_reversePath γ hz
  have hPp : IsOptimalCoupling ν₁ ν₀ (P.map (fun γ => (γ 0,γ 1))) :=
    reversePlan_optimal ν₀ ν₁ plan hp
  have hPc (t : Time) : P.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X := by
    rw [reversePlan_eval]
    exact hcomp (reverseTime t)
  let pair := fun z : C(Time,X) × C(Time,X) => (reversePath z.1,reversePath z.2)
  have hpair : Measurable pair :=
    (measurable_reversePath.comp measurable_fst).prodMk (measurable_reversePath.comp measurable_snd)
  let τ := σ.map pair
  have hτ0 : τ.map Prod.fst = P := by
    dsimp only [τ,P]
    rw [Measure.map_map measurable_fst hpair,←hσ0,
      Measure.map_map measurable_reversePath measurable_fst]
    rfl
  have hτ1 : τ.map Prod.snd = P := by
    dsimp only [τ,P]
    rw [Measure.map_map measurable_snd hpair,←hσ1,
      Measure.map_map measurable_reversePath measurable_snd]
    rfl
  have hτag : ∀ᵐ z ∂τ, ∀ t : Time, t ≤ reverseTime a → z.1 t = z.2 t := by
    apply (ae_map_iff hpair.aemeasurable ?_).mpr
    · filter_upwards [hfuture] with z hz
      intro t ht
      apply hz (reverseTime t)
      change (a:ℝ) ≤ 1-(t:ℝ)
      have ht' : (t:ℝ) ≤ 1-(a:ℝ) := ht
      linarith
    · simpa only [Set.ofPred_forall] using (isClosed_iInter fun t : Time => isClosed_iInter fun _ : t ≤ reverseTime a =>
        (isClosed_eq (by fun_prop) (by fun_prop) :
          IsClosed {z : C(Time,X) × C(Time,X) | z.1 t = z.2 t})).measurableSet
  have hno := hX.compressed_optimal_plan_no_interior_branching K n hn ν₁ ν₀ p hR hs1 hs0
    P hPg hPp C hPc τ hτ0.le hτ1.le (reverseTime a) (by simpa using sub_pos.mpr ha1) hτag
  have hh := ae_of_ae_map hpair.aemeasurable hno
  filter_upwards [hh] with z hz
  have hrev := congrArg reversePath hz
  simpa only [pair,reversePath_reversePath] using hrev

end

 
section

 

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal ProbabilityTheory
variable {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MetricSpace B] [MeasurableSpace B] [BorelSpace B] [SeparableSpace B]

lemma conditional_identity_fiber (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f) :
    ∀ᵐ x ∂ν.map f, ∀ᵐ y ∂condDistrib id f ν x, f y = x := by
  have hgraph : ∀ᵐ z ∂(ν.map f) ⊗ₘ condDistrib id f ν, f z.2 = z.1 := by
    rw [compProd_map_condDistrib hf.aemeasurable measurable_id.aemeasurable]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable ?_).mpr
    · exact Eventually.of_forall fun _ => rfl
    · exact measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst
  exact Measure.ae_ae_of_ae_compProd hgraph

noncomputable def conditionalPair (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) : Measure (A × A) :=
  (condDistrib id f ν ×ₖ condDistrib id f ν) ∘ₘ (ν.map f)

omit [MetricSpace B] [BorelSpace B] [SeparableSpace B] in
lemma conditionalPair_probability (ν : Measure A) [IsProbabilityMeasure ν]
    (f : A → B) (hf : Measurable f) : IsProbabilityMeasure (conditionalPair ν f) := by
  let : IsProbabilityMeasure (ν.map f) :=
    ⟨by rw [Measure.map_apply hf MeasurableSet.univ,Set.preimage_univ,measure_univ]⟩
  unfold conditionalPair
  infer_instance

omit [MetricSpace B] [BorelSpace B] [SeparableSpace B] in
lemma conditionalPair_fst (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f) : (conditionalPair ν f).map Prod.fst = ν := by
  rw [conditionalPair,Measure.map_comp _ _ measurable_fst]
  rw [← Kernel.fst_eq]
  rw [Kernel.fst_prod,condDistrib_comp_map hf.aemeasurable measurable_id.aemeasurable,Measure.map_id]

omit [MetricSpace B] [BorelSpace B] [SeparableSpace B] in
lemma conditionalPair_snd (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f) : (conditionalPair ν f).map Prod.snd = ν := by
  rw [conditionalPair,Measure.map_comp _ _ measurable_snd]
  rw [← Kernel.snd_eq]
  rw [Kernel.snd_prod,condDistrib_comp_map hf.aemeasurable measurable_id.aemeasurable,Measure.map_id]

lemma conditionalPair_fiber (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f) :
    ∀ᵐ z ∂conditionalPair ν f, f z.1 = f z.2 := by
  apply Measure.ae_comp_of_ae_ae
    (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd))
  filter_upwards [conditional_identity_fiber ν f hf] with x hx
  rw [Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd))).mpr
  filter_upwards [hx] with y hy
  filter_upwards [hx] with z hz
  exact hy.trans hz.symm

end

 
section

 

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal ProbabilityTheory
variable {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MetricSpace B] [MeasurableSpace B] [BorelSpace B] [SeparableSpace B]

omit [MetricSpace B] [BorelSpace B] [SeparableSpace B] in
lemma conditionalPair_set_factor (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f)
    (hdiag : ∀ᵐ z ∂conditionalPair ν f, z.1 = z.2)
    {P : Set A} (hP : MeasurableSet P) :
    ∃ S : Set B, MeasurableSet S ∧ ∀ᵐ y ∂ν, y ∈ P ↔ f y ∈ S := by
  let k := condDistrib id f ν
  let S : Set B := {x | k x Pᶜ = 0}
  have hS : MeasurableSet S := measurableSet_eq_fun (k.measurable_coe hP.compl) measurable_const
  have hzero : conditionalPair ν f (P ×ˢ Pᶜ) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hdiag] with z hz
    rintro ⟨h0,h1⟩
    exact h1 (hz ▸ h0)
  have hprod : ∀ᵐ x ∂ν.map f, k x P * k x Pᶜ = 0 := by
    apply (lintegral_eq_zero_iff ((k.measurable_coe hP).mul (k.measurable_coe hP.compl))).mp
    change (∫⁻ x, k x P * k x Pᶜ ∂ν.map f) = 0
    dsimp only [conditionalPair] at hzero
    rw [Measure.bind_apply (hP.prod hP.compl) (Kernel.aemeasurable _)] at hzero
    simpa only [Kernel.prod_apply,Measure.prod_prod] using hzero
  have hevent : MeasurableSet {z : B × A | z.2 ∈ P ↔ z.1 ∈ S} :=
    (measurable_snd hP).iff (measurable_fst hS)
  have hkernel : ∀ᵐ x ∂ν.map f, ∀ᵐ y ∂k x, y ∈ P ↔ x ∈ S := by
    filter_upwards [hprod] with x hx
    by_cases hs : x ∈ S
    · have hp : ∀ᵐ y ∂k x, y ∈ P := by
        have hh := measure_eq_zero_iff_ae_notMem.mp hs
        simpa only [mem_compl_iff,not_not] using hh
      exact hp.mono fun y hy => ⟨fun _ => hs,fun _ => hy⟩
    · have hz : k x P = 0 := (mul_eq_zero.mp hx).resolve_right hs
      exact (measure_eq_zero_iff_ae_notMem.mp hz).mono fun y hy =>
        ⟨fun h => (hy h).elim,fun h => (hs h).elim⟩
  have hall := Measure.ae_compProd_of_ae_ae hevent hkernel
  rw [compProd_map_condDistrib hf.aemeasurable measurable_id.aemeasurable] at hall
  exact ⟨S,hS,ae_of_ae_map (hf.prodMk measurable_id).aemeasurable hall⟩

omit [MetricSpace B] [BorelSpace B] [SeparableSpace B] in
lemma map_mutuallySingular_of_conditionalPair_diagonal
    (ν : Measure A) [IsFiniteMeasure ν] (f : A → B) (hf : Measurable f)
    (hdiag : ∀ᵐ z ∂conditionalPair ν f, z.1 = z.2)
    (ν₀ ν₁ : Measure A) (ha0 : ν₀ ≪ ν) (ha1 : ν₁ ≪ ν) (hs : ν₀ ⟂ₘ ν₁) :
    ν₀.map f ⟂ₘ ν₁.map f := by
  obtain ⟨P,hP,h0,h1⟩ := hs
  obtain ⟨S,hS,he⟩ := conditionalPair_set_factor ν f hf hdiag hP
  refine ⟨S,hS,?_,?_⟩
  · rw [Measure.map_apply hf hS]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ha0.ae_le he,measure_eq_zero_iff_ae_notMem.mp h0] with y hy hz
    exact fun h => hz (hy.mpr h)
  · rw [Measure.map_apply hf hS.compl]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ha1.ae_le he,measure_eq_zero_iff_ae_notMem.mp h1] with y hy hz
    exact fun h => hz (fun hp => h (hy.mp hp))

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_subplans_singular_at
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hcomp : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (ρ₀ ρ₁ : Measure C(Time,X)) (ha0 : ρ₀ ≪ plan) (ha1 : ρ₁ ≪ plan) (hdis : ρ₀ ⟂ₘ ρ₁)
    (a : Time) (ha : 0 < (a:ℝ)) (ha1' : (a:ℝ) < 1) :
    ρ₀.map (fun γ => γ a) ⟂ₘ ρ₁.map (fun γ => γ a) := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨p⟩
  let : Nonempty C(Time,X) := ⟨ContinuousMap.const Time p⟩
  let σ := conditionalPair plan (fun γ => γ a)
  let : IsProbabilityMeasure σ := conditionalPair_probability plan _ (measurable_path_eval a)
  have hno := hX.compressed_optimal_plan_no_interior_crossing K n hn ν₀ ν₁ p hR hs0 hs1
    plan hg hp C hcomp σ
    (conditionalPair_fst plan _ (measurable_path_eval a))
    (conditionalPair_snd plan _ (measurable_path_eval a)) a ha ha1'
    (conditionalPair_fiber plan _ (measurable_path_eval a))
  exact map_mutuallySingular_of_conditionalPair_diagonal plan _ (measurable_path_eval a)
    hno ρ₀ ρ₁ ha0 ha1 hdis

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace InformationTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma lowerSemicontinuous_entropy_compressed_plan
    [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (C : ℝ≥0) (hc : ∀ t : Time, plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • μ)
    (p : X) (R : ℝ)
    (hs : ∀ t : Time, ∀ᵐ x ∂plan.map (fun γ => γ t), dist x p ≤ R) :
    LowerSemicontinuous (fun t : Time => boltzmannEntropy μ (plan.map (fun γ => γ t))) := by
  let π : ProbabilityMeasure C(Time,X) := ⟨plan,inferInstance⟩
  let ν : Time → ProbabilityMeasure X := fun t => π.map (fun γ => γ t)
  let : IsFiniteMeasure (μ.restrict (closedBall p R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p R).measure_lt_top⟩
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro b
  have hclosed := isClosed_compressedKLConstraint (μ.restrict (closedBall p R))
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top ν (fun _ => b+(μ.restrict (closedBall p R)).real univ-1)
    (continuous_time_marginals π) continuous_const
  convert hclosed using 1
  ext t
  exact entropy_bound_localized_iff μ (ν t) measurableSet_closedBall
    ENNReal.ofReal_ne_top (hs t) (hc t) b

lemma NoncollapsedRCD.entropy_compressed_plan_continuousAt_zero
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
      (plan.map (fun γ => γ t))) 0 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let E := fun t : Time => boltzmannEntropy μ (plan.map (fun γ => γ t))
  let q := (K/2)*(wassersteinSq (plan.map (fun γ => γ 0))
     (plan.map (fun γ => γ 1))).toReal
  let G := fun t : Time => (1-(t:ℝ))*E 0+(t:ℝ)*E 1-q*(t:ℝ)*(1-(t:ℝ))
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hG0 : G 0 = E 0 := by simp [G]
  have hbound (t : Time) : E t ≤ G t := by
    let : IsProbabilityMeasure (plan.map (fun γ => γ 0)) := inferInstance
    let : IsProbabilityMeasure (plan.map (fun γ => γ 1)) := inferInstance
    have hh := hX.entropy_convexity_bounded_plan_marginal K n hn _ _ C
      (hc 0) (hc 1) p hR (hs 0) (hs 1) plan hg hp t (hc t)
    convert hh using 1
    dsimp [G,E,q,μ]
    ring
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨lowerSemicontinuous_entropy_compressed_plan μ plan C hc p R hs 0,?_⟩
  intro b hb
  have hh := (hG.continuousAt (x := (0 : Time))).upperSemicontinuousAt b (by simpa only [hG0] using hb)
  exact hh.mono fun t ht => (hbound t).trans_lt ht

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.no_entropy_endpoint_fork
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (P : Fin 3 → Measure C(Time,X)) (hprob : ∀ i, IsProbabilityMeasure (P i))
    (hg : ∀ i, ∀ᵐ γ ∂P i, IsGeodesic γ)
    (hp : ∀ i, IsOptimalCoupling ((P i).map (fun γ => γ 0)) ((P i).map (fun γ => γ 1))
      ((P i).map (fun γ => (γ 0,γ 1))))
    (hmix : P 2 = (1/2:ℝ≥0∞) • (P 0+P 1))
    (C : ℝ≥0) (hc : ∀ i (u : Time),
      (P i).map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ i (u : Time), ∀ᵐ x ∂(P i).map (fun γ => γ u), dist x p ≤ R)
    (he : (P 0).map (fun γ => γ 0) = (P 1).map (fun γ => γ 0))
    (hd : ∀ t : Time, 0 < (t:ℝ) → (t:ℝ) < 1 →
      (P 0).map (fun γ => γ t) ⟂ₘ (P 1).map (fun γ => γ t)) : False := by
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (closedBall p R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p R).measure_lt_top⟩
  let ν := fun i (u : Time) => (P i).map (fun γ => γ u)
  have hνprob (i) (u : Time) : IsProbabilityMeasure (ν i u) := by
    let := hprob i
    infer_instance
  let E := fun i u => boltzmannEntropy μ (ν i u)
  have hmixν (u : Time) : ν 2 u = (1/2:ℝ≥0∞) • (ν 0 u+ν 1 u) := by
    dsimp only [ν]
    rw [hmix,Measure.map_smul _ (measurable_path_eval u).aemeasurable,
      Measure.map_add _ _ (measurable_path_eval u)]
  change ν 0 0 = ν 1 0 at he
  have he2 : ν 2 0 = ν 0 0 := by
    rw [hmixν,←he,←two_smul ℝ≥0∞ _,smul_smul]
    norm_num [ENNReal.inv_mul_cancel]
  have he0 : E 0 0 = E 1 0 := congrArg (boltzmannEntropy μ) he
  have hem : E 2 0 = E 0 0 := congrArg (boltzmannEntropy μ) he2
  have hgap (t : Time) (ht : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
      E 2 t = (E 0 t+E 1 t)/2-Real.log 2 := by
    dsimp only [E]
    rw [hmixν]
    let := hνprob 0 t
    let := hνprob 1 t
    exact entropy_disjoint_probability_midpoint μ (ν 0 t) (ν 1 t)
      (Measure.absolutelyContinuous_of_le_smul (hc 0 t))
      (Measure.absolutelyContinuous_of_le_smul (hc 1 t)) (hd t ht ht1)
      (entropy_integrable_of_bounded_support μ _ ENNReal.ofReal_ne_top (hc 0 t)
        measurableSet_closedBall (hs 0 t))
      (entropy_integrable_of_bounded_support μ _ ENNReal.ofReal_ne_top (hc 1 t)
        measurableSet_closedBall (hs 1 t))
  have hcont (i) : ContinuousAt (E i) 0 := by
    let := hprob i
    exact hX.entropy_compressed_plan_continuousAt_zero K n hn (P i) (hg i) (hp i)
      C (hc i) p hR (hs i)
  let b : ℕ → Time := fun k => ⟨1/((k:ℝ)+2),by
    have hk : (0:ℝ) < (k:ℝ)+2 := by positivity
    constructor
    · positivity
    · exact (div_le_one hk).mpr (by have hh : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)⟩
  have hb0 (k : ℕ) : 0 < (b k:ℝ) := by dsimp [b]; positivity
  have hb1 (k : ℕ) : (b k:ℝ) < 1 := by
    change 1/((k:ℝ)+2) < 1
    exact (div_lt_one (by positivity)).mpr (by have hh : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hlim : Tendsto b atTop (𝓝 (0:Time)) := by
    apply tendsto_subtype_rng.mpr
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 (0:ℝ))).comp
        (tendsto_add_atTop_nat 1)
    convert hh using 1
    simp [b,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc]
    norm_num
  have hlim0 := (hcont 0).tendsto.comp hlim
  have hlim1 := (hcont 1).tendsto.comp hlim
  have hlim2 := (hcont 2).tendsto.comp hlim
  have hEq : E 2 0 = (E 0 0+E 1 0)/2-Real.log 2 := by
    apply tendsto_nhds_unique hlim2
    have hh := ((hlim0.add hlim1).div_const 2).sub_const (Real.log 2)
    exact hh.congr' (Eventually.of_forall fun k => (hgap (b k) (hb0 k) (hb1 k)).symm)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith only [hEq,he0,hem,hlog]


end RegularPointCoordinates

end OAI
