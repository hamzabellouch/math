import Mathlib
import OAI.Analysis.RCDHeat.EndpointCut

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: NormalizedSubplan, OriginalPlanCompression, FiniteCDCompressedPlan, HereditaryCD, EvaluationFactor. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimalPlan_normalized_subplan
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (plan : Measure C(Time,X)) [IsFiniteMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (hcost : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞)
    (κ : Measure C(Time,X)) (hle : κ ≤ plan) (hne : κ univ ≠ 0) :
    let q := (κ univ)⁻¹ • κ
    IsProbabilityMeasure q ∧ (∀ᵐ γ ∂q, IsGeodesic γ) ∧
    IsOptimalCoupling (q.map (fun γ => γ 0)) (q.map (fun γ => γ 1))
      (q.map (fun γ => (γ 0,γ 1))) ∧
    (q.map (fun γ => γ 0) ≤ (κ univ)⁻¹ • ν₀) ∧
    (q.map (fun γ => γ 1) ≤ (κ univ)⁻¹ • ν₁) := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le plan hle
  let : NeZero κ := ⟨by intro he; apply hne; rw [he]; rfl⟩
  let q := (κ univ)⁻¹ • κ
  have hfin : κ univ ≠ ∞ := measure_ne_top _ _
  have ha0 : (κ univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hfin
  have haf : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hne
  have hm := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  have hpκ := hp.subcoupling hcost (Measure.map_mono hle hm)
  have he0 : (κ.map (fun γ => (γ 0,γ 1))).map Prod.fst = κ.map (fun γ => γ 0) := by
    rw [Measure.map_map measurable_fst hm]; rfl
  have he1 : (κ.map (fun γ => (γ 0,γ 1))).map Prod.snd = κ.map (fun γ => γ 1) := by
    rw [Measure.map_map measurable_snd hm]; rfl
  rw [he0,he1] at hpκ
  have hqp : IsOptimalCoupling (q.map (fun γ => γ 0)) (q.map (fun γ => γ 1))
      (q.map (fun γ => (γ 0,γ 1))) := by
    simpa only [q,Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable,
      Measure.map_smul _ hm.aemeasurable] using hpκ.smul ha0 haf
  have hep := optimalPlan_endpoints ν₀ ν₁ plan hp
  have hle0 : κ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [←hep.1]; exact Measure.map_mono hle (measurable_path_eval 0)
  have hle1 : κ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [←hep.2]; exact Measure.map_mono hle (measurable_path_eval 1)
  refine ⟨inferInstance,?_,hqp,?_,?_⟩
  · exact (hg.filter_mono (ae_mono hle)).filter_mono Measure.smul_absolutelyContinuous.ae_le
  · rw [Measure.map_smul _ (measurable_path_eval 0).aemeasurable]
    intro S
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_right (hle0 S) _
  · rw [Measure.map_smul _ (measurable_path_eval 1).aemeasurable]
    intro S
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_right (hle1 S) _


 
theorem NoncollapsedRCD.optimal_plan_ac_marginal_compression
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (C : ℝ) (hC : 0 < C)
    (h0 : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (h1 : ν₁ ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (s : Time) (hac : plan.map (fun γ => γ s) ≪ hausdorff n X) :
    plan.map (fun γ => γ s) ≤
      ENNReal.ofReal (C*Real.exp (max (-K) 0*R^2/2)) • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let ν := plan.map (fun γ => γ s)
  let : IsProbabilityMeasure ν := inferInstance
  let A := max (-K) 0*R^2/2
  let D := C*Real.exp A
  have hD : 0 < D := mul_pos hC (Real.exp_pos _)
  change ν ≤ ENNReal.ofReal D • μ
  by_contra hbad
  obtain ⟨M,hM,hpos⟩ := exists_positive_density_slab μ ν hac hD hbad
  let B := {x | D < (ν.rnDeriv μ x).toReal ∧ (ν.rnDeriv μ x).toReal ≤ M}
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_const (ν.measurable_rnDeriv μ).ennreal_toReal).inter
      (measurableSet_le (ν.measurable_rnDeriv μ).ennreal_toReal measurable_const)
  let κ := plan.restrict ((fun γ => γ s) ⁻¹' B)
  have hκ : κ ≤ plan := Measure.restrict_le_self
  have hκmap : κ.map (fun γ => γ s) = ν.restrict B :=
    (Measure.restrict_map (measurable_path_eval s) hB).symm
  have hκ0 : κ univ ≠ 0 := by
    change (plan.restrict ((fun γ => γ s) ⁻¹' B)) univ ≠ 0
    rw [Measure.restrict_apply_univ]
    exact (show ν B = plan ((fun γ => γ s) ⁻¹' B) from
      Measure.map_apply (measurable_path_eval s) hB) ▸ hpos
  let : IsFiniteMeasure κ := inferInstanceAs (IsFiniteMeasure (plan.restrict _))
  have hκfin : κ univ ≠ ∞ := measure_ne_top _ _
  let a := (κ univ)⁻¹
  have ha : a ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  have ha0 : a ≠ 0 := ENNReal.inv_ne_zero.mpr hκfin
  have har : 0 < a.toReal := ENNReal.toReal_pos ha0 ha
  let q := a • κ
  have hc : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [←wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le ν₀ p hs0)
      (finiteSecondMoment_of_ae_dist_le ν₁ p hs1)
  obtain ⟨hq,hqg,hqp,hq0,hq1⟩ := optimalPlan_normalized_subplan ν₀ ν₁ plan hg hp hc κ hκ hκ0
  let : IsProbabilityMeasure q := hq
  let η₀ := q.map (fun γ => γ 0)
  let η₁ := q.map (fun γ => γ 1)
  let η := q.map (fun γ => γ s)
  let : IsProbabilityMeasure η₀ := inferInstance
  let : IsProbabilityMeasure η₁ := inferInstance
  let : IsProbabilityMeasure η := inferInstance
  have hm : η = a • ν.restrict B := by
    change (a • κ).map (fun γ => γ s) = a • ν.restrict B
    rw [Measure.map_smul _ (measurable_path_eval s).aemeasurable,hκmap]
  have hS := restricted_density_slab_bounds μ ν hac hM.le B hB (fun _ hx => hx) ha ha0
  rw [←hm] at hS
  have hbound0 : η₀ ≤ ENNReal.ofReal (a.toReal*C) • μ := by
    calc
      η₀ ≤ a • ν₀ := hq0
      _ ≤ a • (ENNReal.ofReal C • μ) := _root_.smul_le_smul_left a h0
      _ = _ := by rw [smul_smul,ENNReal.ofReal_mul (le_of_lt har),ENNReal.ofReal_toReal ha]
  have hbound1 : η₁ ≤ ENNReal.ofReal (a.toReal*C) • μ := by
    calc
      η₁ ≤ a • ν₁ := hq1
      _ ≤ a • (ENNReal.ofReal C • μ) := _root_.smul_le_smul_left a h1
      _ = _ := by rw [smul_smul,ENNReal.ofReal_mul (le_of_lt har),ENNReal.ofReal_toReal ha]
  have hsη0 : ∀ᵐ x ∂η₀, dist x p ≤ R :=
    hs0.filter_mono (Measure.absolutelyContinuous_of_le_smul hq0).ae_le
  have hsη1 : ∀ᵐ x ∂η₁, dist x p ≤ R :=
    hs1.filter_mono (Measure.absolutelyContinuous_of_le_smul hq1).ae_le
  have hupper := hX.entropy_plan_marginal_le_log_capacity K n hn η₀ η₁ (mul_pos har hC)
    hbound0 hbound1 p hR hsη0 hsη1 q hqg hqp s hS.1
  have hsη : ∀ᵐ x ∂η, x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ q hqg hqp p hR hsη0 hsη1).mono fun γ hγ => hγ.2 s
  let : IsFiniteMeasure (μ.restrict (closedBall p (3*R))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall p (3*R)).measure_lt_top⟩
  have hEnt := entropy_integrable_of_bounded_support μ η ENNReal.ofReal_ne_top hS.1
    measurableSet_closedBall hsη
  have hlower := log_density_floor_lt_entropy μ η (Measure.absolutelyContinuous_of_le_smul hS.1)
    hEnt (mul_pos har hD) hS.2
  have hlog : Real.log (a.toReal*D) = Real.log (a.toReal*C)+A := by
    rw [show a.toReal*D = (a.toReal*C)*Real.exp A by dsimp [D]; ring,
      Real.log_mul (mul_pos har hC).ne' (Real.exp_pos _).ne',Real.log_exp]
  rw [hlog] at hlower
  exact (not_lt_of_ge hupper) hlower


 
theorem NoncollapsedRCD.exists_bounded_compression_fullCD_plan
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (C : ℝ) (hC : 0 < C)
    (h0 : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (h1 : ν₁ ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ plan : Measure C(Time, X),
      IsProbabilityMeasure plan ∧ (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (Measure.map (fun γ => (γ 0, γ 1)) plan) ∧
      (∀ (N : ℝ), (n : ℝ) ≤ N → ∀ t : Time,
        (∫⁻ γ,
          tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)) *
            (ν₀.rnDeriv (hausdorff n X) (γ 0)) ^ (-(1 / N)) +
          tau K N (t : ℝ) (dist (γ 0) (γ 1)) *
            (ν₁.rnDeriv (hausdorff n X) (γ 1)) ^ (-(1 / N)) ∂plan) ≤
          renyiIntegral (hausdorff n X) (Measure.map (fun γ => γ t) plan) N) ∧
      ∀ t : Time, Measure.map (fun γ => γ t) plan ≤
        ENNReal.ofReal (C * Real.exp (max (-K) 0 * R^2 / 2)) • hausdorff n X
 := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (closedBall p (3*R))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall p (3*R)).measure_lt_top⟩
  have ha0 := Measure.absolutelyContinuous_of_le_smul h0
  have ha1 := Measure.absolutelyContinuous_of_le_smul h1
  obtain ⟨plan,hplan,hg,hp,hineq⟩ := hX.cd ν₀ ν₁ inferInstance inferInstance ha0 ha1
    (finiteSecondMoment_of_ae_dist_le ν₀ p hs0) (finiteSecondMoment_of_ae_dist_le ν₁ p hs1)
  let := hplan
  refine ⟨plan,hplan,hg,hp,hineq,fun t => ?_⟩
  let ν := plan.map (fun γ => γ t)
  let : IsProbabilityMeasure ν := inferInstance
  have hs : ∀ᵐ x ∂ν, x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ plan hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hhalf := density_rpow_half_integrable_of_supported μ ν measurableSet_closedBall hs
  have hac := cd_plan_absolutelyContinuous_half μ K n ν₀ ν₁ ha0 ha1 plan hp t
    (fun N hN => hineq N hN t) hhalf
  exact hX.optimal_plan_ac_marginal_compression K n hn ν₀ ν₁ C hC h0 h1 p hR hs0 hs1
    plan hg hp t hac


 
theorem NoncollapsedRCD.compressed_optimal_plan_fullCD
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X) :
      ∀ (N : ℝ), (n : ℝ) ≤ N → ∀ t : Time,
        (∫⁻ γ,
          tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)) *
            (ν₀.rnDeriv (hausdorff n X) (γ 0)) ^ (-(1 / N)) +
          tau K N (t : ℝ) (dist (γ 0) (γ 1)) *
            (ν₁.rnDeriv (hausdorff n X) (γ 1)) ^ (-(1 / N)) ∂plan) ≤
          renyiIntegral (hausdorff n X) (Measure.map (fun γ => γ t) plan) N := by
  have he := optimalPlan_endpoints ν₀ ν₁ plan hp
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
  have h0 : ν₀ ≤ ENNReal.ofReal C' • hausdorff n X := by simpa only [he.1] using hc' 0
  have h1 : ν₁ ≤ ENNReal.ofReal C' • hausdorff n X := by simpa only [he.2] using hc' 1
  obtain ⟨Q,hQprob,hQg,hQp,hQcd,hQc⟩ :=
    hX.exists_bounded_compression_fullCD_plan K n hn ν₀ ν₁ C' hC' h0 h1 p hR hs0 hs1
  let := hQprob
  let D : ℝ≥0 := ⟨max (C:ℝ) (C'*Real.exp (max (-K) 0*R^2/2)),le_max_of_le_left C.2⟩
  have hpc (t : Time) : plan.map (fun γ => γ t) ≤ ENNReal.ofReal D • hausdorff n X := by
    apply (hc t).trans
    apply Measure.le_iff.mpr
    intro S hS
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
    exact (le_max_left (C:ℝ) (C'*Real.exp (max (-K) 0*R^2/2)))
  have hqc (t : Time) : Q.map (fun γ => γ t) ≤ ENNReal.ofReal D • hausdorff n X := by
    apply (hQc t).trans
    apply Measure.le_iff.mpr
    intro S hS
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
    exact (le_max_right (C:ℝ) (C'*Real.exp (max (-K) 0*R^2/2)))
  have heq := hX.compressed_optimal_plan_unique K n hn ν₀ ν₁ p hR hs0 hs1
    plan Q hg hQg hp hQp D hpc hqc
  simpa only [heq] using hQcd

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma NoncollapsedRCD.evaluation_conditionalPair_diagonal
    [CompleteSpace X] [SeparableSpace X] [Nonempty C(Time,X)]
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (t : Time) :
    ∀ᵐ z ∂conditionalPair plan (fun γ => γ t), z.1 = z.2 := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty C(Time,X) := ⟨ContinuousMap.const Time p⟩
  let σ := conditionalPair plan (fun γ => γ t)
  let : IsProbabilityMeasure σ := conditionalPair_probability plan _ (measurable_path_eval t)
  have hσ0 : σ.map Prod.fst = plan := conditionalPair_fst plan _ (measurable_path_eval t)
  have hσ1 : σ.map Prod.snd = plan := conditionalPair_snd plan _ (measurable_path_eval t)
  have hagree : ∀ᵐ z ∂σ, z.1 t = z.2 t := conditionalPair_fiber plan _ (measurable_path_eval t)
  by_cases ht0 : t = 0
  · subst t
    exact hX.compressed_optimal_plan_no_endpoint_fork K n hn ν₀ ν₁ p hR hs0 hs1
      plan hg hp C hc σ hσ0.le hσ1.le hagree
  by_cases ht1 : t = 1
  · subst t
    let P := plan.map reversePath
    let : IsProbabilityMeasure P := inferInstance
    have hPg : ∀ᵐ γ ∂P, IsGeodesic γ := by
      apply (ae_map_iff measurable_reversePath.aemeasurable isClosed_geodesicSet.measurableSet).mpr
      exact hg.mono fun γ hz => isGeodesic_reversePath γ hz
    have hPp := reversePlan_optimal ν₀ ν₁ plan hp
    have hPc (s : Time) : P.map (fun γ => γ s) ≤ ENNReal.ofReal C • hausdorff n X := by
      rw [reversePlan_eval]
      exact hc (reverseTime s)
    let pair := fun z : C(Time,X) × C(Time,X) => (reversePath z.1,reversePath z.2)
    have hpair : Measurable pair :=
      (measurable_reversePath.comp measurable_fst).prodMk (measurable_reversePath.comp measurable_snd)
    let τ := σ.map pair
    let : IsProbabilityMeasure τ := inferInstance
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
    have hτa : ∀ᵐ z ∂τ, z.1 0 = z.2 0 := by
      apply (ae_map_iff hpair.aemeasurable ?_).mpr
      · simpa only [pair,reversePath_apply,reverseTime_zero] using hagree
      · exact (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
    have hh := hX.compressed_optimal_plan_no_endpoint_fork K n hn ν₁ ν₀ p hR hs1 hs0
      P hPg hPp C hPc τ hτ0.le hτ1.le hτa
    have hh' := ae_of_ae_map hpair.aemeasurable hh
    filter_upwards [hh'] with z hz
    have hrev := congrArg reversePath hz
    simpa only [pair,reversePath_reversePath] using hrev
  · exact hX.compressed_optimal_plan_no_interior_crossing K n hn ν₀ ν₁ p hR hs0 hs1
      plan hg hp C hc σ hσ0 hσ1 t
      (lt_of_le_of_ne t.2.1 (fun h => ht0 (Subtype.ext h.symm)))
      (lt_of_le_of_ne t.2.2 (fun h => ht1 (Subtype.ext h))) hagree

lemma NoncollapsedRCD.compressed_plan_evaluation_set_factor
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (t : Time) {P : Set C(Time,X)} (hP : MeasurableSet P) :
    ∃ S : Set X, MeasurableSet S ∧ ∀ᵐ γ ∂plan, γ ∈ P ↔ γ t ∈ S := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty C(Time,X) := ⟨ContinuousMap.const Time p⟩
  exact conditionalPair_set_factor plan _ (measurable_path_eval t)
    (hX.evaluation_conditionalPair_diagonal K n hn ν₀ ν₁ p hR hs0 hs1 plan hg hp C hc t) hP


end RegularPointCoordinates

end OAI
