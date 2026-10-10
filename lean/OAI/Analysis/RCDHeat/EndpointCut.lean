import Mathlib
import OAI.Analysis.RCDHeat.ForkPlans
import OAI.Analysis.RCDHeat.Noncrossing

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EndpointCut, EndpointPair, ConditionalUnique, Uniqueness, DensitySlab. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.no_coupled_endpoint_cut
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ u : Time,
      plan.map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ u : Time, ∀ᵐ x ∂plan.map (fun γ => γ u), dist x p ≤ R)
    (σ : Measure (C(Time,X) × C(Time,X))) [IsFiniteMeasure σ] (hne : σ univ ≠ 0)
    (hσ0 : σ.map Prod.fst ≤ plan) (hσ1 : σ.map Prod.snd ≤ plan)
    (hagree : ∀ᵐ z ∂σ, z.1 0 = z.2 0)
    (S : Set C(Time,X)) (hS : MeasurableSet S)
    (hdis : ∀ᵐ z ∂σ, z.1 ∈ S ∧ z.2 ∉ S) : False := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : IsProbabilityMeasure (plan.map (fun γ => γ 0)) := inferInstance
  let : IsProbabilityMeasure (plan.map (fun γ => γ 1)) := inferInstance
  let Q : Fin 3 → Measure C(Time,X) := ![σ.map Prod.fst,σ.map Prod.snd,
      (1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map Prod.snd)]
  let a := (σ univ)⁻¹
  let P := fun i => a • Q i
  let D := a.toReal*(2*C)
  have habs : a ≠ ∞ := ENNReal.inv_ne_top.mpr hne
  have ha0 : a ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top σ univ)
  have ha : 0 < a.toReal := ENNReal.toReal_pos ha0 habs
  have hD : 0 < D := mul_pos ha (mul_pos (by norm_num) hC)
  obtain ⟨hmass,hdom,heval⟩ := coupled_fork_unscaled plan σ hσ0 hσ1 Prod.snd measurable_snd
    (hagree.mono fun z hz => ⟨hz.symm,rfl,hz⟩)
    (fun _ => Eventually.of_forall fun _ => Or.inr rfl)
  change ∀ i, Q i univ = σ univ at hmass
  change ∀ i, (Q i).map (fun γ => (γ 0,γ 1)) ≤ _ at hdom
  change ∀ i (u : Time), (Q i).map (fun γ => γ u) ≤ _ at heval
  have hQfin (i) : IsFiniteMeasure (Q i) := by
    exact ⟨by rw [hmass i]; exact measure_lt_top σ univ⟩
  have hcost : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [←wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le _ p (hs 0))
      (finiteSecondMoment_of_ae_dist_le _ p (hs 1))
  have hprob (i) : IsProbabilityMeasure (P i) := by
    let := hQfin i
    have hh := (optimalPlan_normalize_endpoint_dom plan (Q i) hp hcost (hdom i)
      (by rwa [hmass i])).1
    simpa only [hmass] using hh
  have hopt (i) : IsOptimalCoupling ((P i).map (fun γ => γ 0)) ((P i).map (fun γ => γ 1))
      ((P i).map (fun γ => (γ 0,γ 1))) := by
    let := hQfin i
    have hh := (optimalPlan_normalize_endpoint_dom plan (Q i) hp hcost (hdom i)
      (by rwa [hmass i])).2
    simpa only [hmass] using hh
  have hQg0 : ∀ᵐ γ ∂Q 0, IsGeodesic γ := hg.filter_mono (ae_mono hσ0)
  have hQg1 : ∀ᵐ γ ∂Q 1, IsGeodesic γ := by
    exact hg.filter_mono (ae_mono hσ1)
  have hQg2 : ∀ᵐ γ ∂Q 2, IsGeodesic γ :=
    (ae_add_measure_iff.mpr ⟨hQg0,hQg1⟩).filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hgeo (i) : ∀ᵐ γ ∂P i, IsGeodesic γ := by
    have hgi : ∀ᵐ γ ∂Q i, IsGeodesic γ := by
      fin_cases i
      · exact hQg0
      · exact hQg1
      · exact hQg2
    exact hgi.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hPdom (i) (u : Time) : (P i).map (fun γ => γ u) ≤
      (a*2) • plan.map (fun γ => γ u) := by
    dsimp only [P]
    rw [Measure.map_smul _ (measurable_path_eval u).aemeasurable,←smul_smul]
    exact _root_.smul_le_smul_left a (heval i u)
  have hcomp (i) (u : Time) : (P i).map (fun γ => γ u) ≤ ENNReal.ofReal D • hausdorff n X := by
    apply (hPdom i u).trans
    have hh := _root_.smul_le_smul_left (a*2) (hc u)
    convert hh using 1
    rw [smul_smul]
    congr 1
    dsimp only [D]
    rw [ENNReal.ofReal_mul ha.le,ENNReal.ofReal_toReal habs,ENNReal.ofReal_mul (by norm_num)]
    norm_num
    ring
  have hsupport (i) (u : Time) : ∀ᵐ x ∂(P i).map (fun γ => γ u), dist x p ≤ R :=
    (hs u).filter_mono (Measure.absolutelyContinuous_of_le_smul (hPdom i u)).ae_le
  have hmix : P 2 = (1/2:ℝ≥0∞) • (P 0+P 1) := by
    change a • ((1/2:ℝ≥0∞) • (σ.map Prod.fst+σ.map Prod.snd)) =
      (1/2:ℝ≥0∞) • (a • σ.map Prod.fst+a • σ.map Prod.snd)
    rw [←smul_add,smul_smul,smul_smul,mul_comm]
  have heq : (P 0).map (fun γ => γ 0) = (P 1).map (fun γ => γ 0) := by
    change (a • σ.map Prod.fst).map _ = (a • σ.map Prod.snd).map _
    rw [Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_map (measurable_path_eval 0) measurable_fst,
      Measure.map_map (measurable_path_eval 0) measurable_snd]
    exact congrArg (a • ·) (Measure.map_congr hagree)
  have haP0 : P 0 ≪ plan :=
    (Measure.absolutelyContinuous_of_le hσ0).smul_left a
  have haP1 : P 1 ≪ plan :=
    (Measure.absolutelyContinuous_of_le hσ1).smul_left a
  have hsing : P 0 ⟂ₘ P 1 := by
    apply Measure.MutuallySingular.mk (s := Sᶜ) (t := S)
    · change (a • σ.map Prod.fst) Sᶜ = 0
      rw [Measure.smul_apply,Measure.map_apply measurable_fst hS.compl]
      have hh : σ (Prod.fst ⁻¹' Sᶜ) = 0 :=
        ae_iff.mp (hdis.mono fun z hz => by simpa using hz.1)
      simp only [hh,smul_eq_mul,mul_zero]
    · change (a • σ.map Prod.snd) S = 0
      rw [Measure.smul_apply,Measure.map_apply measurable_snd hS]
      have hh : σ (Prod.snd ⁻¹' S) = 0 :=
        measure_eq_zero_iff_ae_notMem.mpr (hdis.mono fun z hz => hz.2)
      simp only [hh,smul_eq_mul,mul_zero]
    · intro x _
      exact (em (x ∈ S)).symm
  have hsing_t (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
      (P 0).map (fun γ => γ t) ⟂ₘ (P 1).map (fun γ => γ t) :=
    hX.compressed_subplans_singular_at K n hn _ _ p hR (hs 0) (hs 1) plan hg hp
      ⟨C,hC.le⟩ hc (P 0) (P 1) haP0 haP1 hsing t ht0 ht1
  exact hX.no_entropy_endpoint_fork K n hn P hprob hgeo hopt hmix ⟨D,hD.le⟩ hcomp p hR hsupport heq hsing_t


 
theorem NoncollapsedRCD.compressed_optimal_plan_no_endpoint_fork
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (σ : Measure (C(Time,X) × C(Time,X))) [IsFiniteMeasure σ]
    (hσ0 : σ.map Prod.fst ≤ plan) (hσ1 : σ.map Prod.snd ≤ plan)
    (hagree : ∀ᵐ z ∂σ, z.1 0 = z.2 0) : ∀ᵐ z ∂σ, z.1 = z.2 := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  have he := optimalPlan_endpoints ν₀ ν₁ plan hp
  have hp' : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
  have hs (t : Time) : ∀ᵐ x ∂plan.map (fun γ => γ t), dist x p ≤ 3*R := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ plan hg hp p hR hs0 hs1).mono fun γ hz => hz.2 t
  let C' := (C:ℝ)+1
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hc' (t : Time) : plan.map (fun γ => γ t) ≤ ENNReal.ofReal C' • hausdorff n X := by
    apply (hc t).trans
    apply Measure.le_iff.mpr
    intro S hS
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
    dsimp [C']
    linarith
  rw [ae_iff]
  by_contra hne
  obtain ⟨S,hS,hcut⟩ := exists_measurable_directed_cut σ Prod.fst Prod.snd measurable_fst measurable_snd
  let A := {z : C(Time,X) × C(Time,X) | z.1 ∈ S ∧ z.2 ∉ S}
  have hA : MeasurableSet A := (measurable_fst hS).inter (measurable_snd hS.compl)
  have hAn : (σ.restrict A) univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    intro hh
    rw [hh] at hcut
    have hz := le_antisymm hcut bot_le
    have hd : σ {z : C(Time,X) × C(Time,X) | z.1 ≠ z.2} = 0 := by
      simpa only [ENNReal.div_eq_zero_iff,show (16:ℝ≥0∞) ≠ ∞ by norm_num,or_false] using hz
    exact hne hd
  exact hX.no_coupled_endpoint_cut K n hn plan hg hp' hC' hc' p
    (mul_nonneg (by norm_num) hR) hs (σ.restrict A) hAn
    ((Measure.map_mono Measure.restrict_le_self measurable_fst).trans hσ0)
    ((Measure.map_mono Measure.restrict_le_self measurable_snd).trans hσ1)
    (hagree.filter_mono (ae_mono Measure.restrict_le_self)) S hS (ae_restrict_mem hA)

end

 
section

 

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal ProbabilityTheory
variable {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MetricSpace B] [MeasurableSpace B] [BorelSpace B] [SeparableSpace B]

omit [MetricSpace B] [BorelSpace B] [SeparableSpace B] in
lemma measure_eq_of_conditionalPair_diagonal
    (ν : Measure A) [IsFiniteMeasure ν] (f : A → B) (hf : Measurable f)
    (hdiag : ∀ᵐ z ∂conditionalPair ν f, z.1 = z.2)
    (ν₀ ν₁ : Measure A) (ha0 : ν₀ ≪ ν) (ha1 : ν₁ ≪ ν)
    (he : ν₀.map f = ν₁.map f) : ν₀ = ν₁ := by
  apply Measure.ext
  intro P hP
  obtain ⟨S,hS,hfactor⟩ := conditionalPair_set_factor ν f hf hdiag hP
  have hset : P =ᵐ[ν] f ⁻¹' S := hfactor.mono fun _ hz => propext hz
  calc
    ν₀ P = ν₀ (f ⁻¹' S) := measure_congr (ha0.ae_le hset)
    _ = ν₀.map f S := (Measure.map_apply hf hS).symm
    _ = ν₁.map f S := congrArg (fun μ : Measure B => μ S) he
    _ = ν₁ (f ⁻¹' S) := Measure.map_apply hf hS
    _ = ν₁ P := (measure_congr (ha1.ae_le hset)).symm

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_optimal_plan_unique
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan₀ plan₁ : Measure C(Time,X))
    [IsProbabilityMeasure plan₀] [IsProbabilityMeasure plan₁]
    (hg0 : ∀ᵐ γ ∂plan₀, IsGeodesic γ) (hg1 : ∀ᵐ γ ∂plan₁, IsGeodesic γ)
    (hp0 : IsOptimalCoupling ν₀ ν₁ (plan₀.map (fun γ => (γ 0,γ 1))))
    (hp1 : IsOptimalCoupling ν₀ ν₁ (plan₁.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0)
    (hc0 : ∀ t : Time, plan₀.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hc1 : ∀ t : Time, plan₁.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X) :
    plan₀ = plan₁ := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty C(Time,X) := ⟨ContinuousMap.const Time p⟩
  let M := measureMixture (1/2) plan₀ plan₁
  let : IsProbabilityMeasure M := measureMixture_probability (by norm_num) (by norm_num)
  have hMg : ∀ᵐ γ ∂M, IsGeodesic γ := ae_add_measure_iff.mpr
    ⟨hg0.filter_mono Measure.smul_absolutelyContinuous.ae_le,
      hg1.filter_mono Measure.smul_absolutelyContinuous.ae_le⟩
  have hMp : IsOptimalCoupling ν₀ ν₁ (M.map (fun γ => (γ 0,γ 1))) := by
    dsimp only [M]
    rw [measureMixture_map _ _ _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    exact hp0.mixture hp1 (by norm_num) (by norm_num)
  have hMc (t : Time) : M.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X := by
    dsimp only [M]
    rw [measureMixture_map _ _ _ (measurable_path_eval t)]
    calc
      _ ≤ measureMixture (1/2) (ENNReal.ofReal C • hausdorff n X) (ENNReal.ofReal C • hausdorff n X) :=
        add_le_add (_root_.smul_le_smul_left _ (hc0 t)) (_root_.smul_le_smul_left _ (hc1 t))
      _ = _ := measureMixture_self _ (by norm_num) (by norm_num)
  let σ := conditionalPair M (fun γ => γ 0)
  let : IsProbabilityMeasure σ := conditionalPair_probability M _ (measurable_path_eval 0)
  have hd := hX.compressed_optimal_plan_no_endpoint_fork K n hn ν₀ ν₁ p hR hs0 hs1
    M hMg hMp C hMc σ
    (conditionalPair_fst M _ (measurable_path_eval 0)).le
    (conditionalPair_snd M _ (measurable_path_eval 0)).le
    (conditionalPair_fiber M _ (measurable_path_eval 0))
  have ha0 : plan₀ ≪ M := by
    exact (Measure.absolutelyContinuous_smul (c := ENNReal.ofReal (1-(1/2:ℝ))) (by norm_num)).trans
      (Measure.absolutelyContinuous_of_le (le_add_of_nonneg_right bot_le))
  have ha1 : plan₁ ≪ M := by
    exact (Measure.absolutelyContinuous_smul (c := ENNReal.ofReal (1/2:ℝ)) (by norm_num)).trans
      (Measure.absolutelyContinuous_of_le (le_add_of_nonneg_left bot_le))
  apply measure_eq_of_conditionalPair_diagonal M _ (measurable_path_eval 0) hd plan₀ plan₁ ha0 ha1
  exact (optimalPlan_endpoints ν₀ ν₁ plan₀ hp0).1.trans
    (optimalPlan_endpoints ν₀ ν₁ plan₁ hp1).1.symm

end

 

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
variable {X : Type*} [MeasurableSpace X]

theorem exists_positive_density_slab (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] (hac : ν ≪ μ) {D : ℝ} (hD : 0 < D)
    (hbad : ¬ ν ≤ ENNReal.ofReal D • μ) :
    ∃ M : ℝ, 0 < M ∧ ν {x | D < (ν.rnDeriv μ x).toReal ∧ (ν.rnDeriv μ x).toReal ≤ M} ≠ 0 := by
  have hpos : ν {x | D < (ν.rnDeriv μ x).toReal} ≠ 0 := by
    intro hz
    have hν : ∀ᵐ x ∂ν, ¬ D < (ν.rnDeriv μ x).toReal := by
      simpa only [ae_iff,not_not] using hz
    have hμ := Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hν
    apply hbad
    rw [←Measure.withDensity_rnDeriv_eq ν μ hac,←withDensity_const]
    apply withDensity_mono
    filter_upwards [hμ,Measure.rnDeriv_lt_top ν μ] with x hx hxt
    by_cases hn : ν.rnDeriv μ x = 0
    · simp only [hn]; exact zero_le
    · rw [←ENNReal.ofReal_toReal hxt.ne]
      exact (ENNReal.ofReal_le_ofReal_iff hD.le).mpr (le_of_not_gt (hx hn))
  have hu : {x | D < (ν.rnDeriv μ x).toReal} =
      ⋃ k : ℕ, {x | D < (ν.rnDeriv μ x).toReal ∧ (ν.rnDeriv μ x).toReal ≤ (k+1:ℕ)} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := exists_nat_gt (ν.rnDeriv μ x).toReal
      exact ⟨k,hx,hk.le.trans (by exact_mod_cast Nat.le_succ k)⟩
    · rintro ⟨k,hk⟩
      exact hk.1
  rw [hu] at hpos
  by_contra! hall
  apply hpos
  apply measure_iUnion_null
  intro k
  exact hall (k+1:ℕ) (by positivity)

theorem restricted_density_slab_bounds (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] (hac : ν ≪ μ) {D M : ℝ} (hM : 0 ≤ M)
    (B : Set X) (hB : MeasurableSet B)
    (hBdef : ∀ x ∈ B, D < (ν.rnDeriv μ x).toReal ∧ (ν.rnDeriv μ x).toReal ≤ M)
    {a : ℝ≥0∞} (ha : a ≠ ∞) (ha0 : a ≠ 0) :
    a • ν.restrict B ≤ ENNReal.ofReal (a.toReal*M) • μ ∧
    ∀ᵐ x ∂a • ν.restrict B, a.toReal*D < ((a • ν.restrict B).rnDeriv μ x).toReal := by
  have hac' : a • ν.restrict B ≪ μ := Measure.smul_absolutelyContinuous.trans
    ((Measure.restrict_le_self).absolutelyContinuous.trans hac)
  have hr : (a • ν.restrict B).rnDeriv μ =ᵐ[μ]
      fun x => a*(B.indicator (ν.rnDeriv μ) x) := by
    filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (ν.restrict B) μ ha,
      Measure.rnDeriv_restrict ν μ hB] with x hx hy
    simp only [hx,hy,Pi.smul_apply,smul_eq_mul]
  have hrbound : ∀ᵐ x ∂μ, (a • ν.restrict B).rnDeriv μ x ≤ ENNReal.ofReal (a.toReal*M) := by
    filter_upwards [hr,Measure.rnDeriv_lt_top ν μ] with x hx hxt
    rw [hx]
    by_cases hxb : x ∈ B
    · rw [indicator_of_mem hxb,ENNReal.ofReal_mul (ENNReal.toReal_nonneg),ENNReal.ofReal_toReal ha]
      have hh := (ENNReal.toReal_le_toReal hxt.ne ENNReal.ofReal_ne_top).mp
        ((hBdef x hxb).2.trans_eq (ENNReal.toReal_ofReal hM).symm)
      gcongr
    · rw [indicator_of_notMem hxb,mul_zero]
      exact zero_le
  constructor
  · calc
      a • ν.restrict B = μ.withDensity ((a • ν.restrict B).rnDeriv μ) :=
        (Measure.withDensity_rnDeriv_eq _ _ hac').symm
      _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (a.toReal*M)) := withDensity_mono hrbound
      _ = ENNReal.ofReal (a.toReal*M) • μ := withDensity_const _
  · have hmem : ∀ᵐ x ∂a • ν.restrict B, x ∈ B :=
      (ae_restrict_mem hB).filter_mono Measure.smul_absolutelyContinuous.ae_le
    filter_upwards [hac'.ae_le hr,hmem] with x hx hxb
    rw [hx,indicator_of_mem hxb,ENNReal.toReal_mul]
    exact mul_lt_mul_of_pos_left (hBdef x hxb).1 (ENNReal.toReal_pos ha0 ha)


end RegularPointCoordinates

end OAI
