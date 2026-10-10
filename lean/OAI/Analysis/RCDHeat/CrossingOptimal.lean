import Mathlib
import OAI.Analysis.RCDHeat.EntropyPlanExtension
import OAI.Analysis.RCDHeat.LastTimeBins

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CrossingOptimal, ReversePlan, CrossingForward. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma transportCost_map_pair {A : Type*} [MeasurableSpace A] [SeparableSpace X]
    (σ : Measure A) (f g : A → X) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun z => dist (f z) (g z)^2) σ) :
    transportCost (σ.map (fun z => (f z,g z))) =
      ENNReal.ofReal (∫ z, dist (f z) (g z)^2 ∂σ) := by
  rw [transportCost,lintegral_map
    ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2) (hf.prodMk hg)]
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro z
  exact (ENNReal.ofReal_pow dist_nonneg 2).symm

lemma crossing_optimal_lengths [SeparableSpace X]
    (ν₀ ν₁ : Measure X) (plan : Measure C(Time,X))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) plan)
    (σ : Measure (C(Time,X) × C(Time,X)))
    (hσ0 : σ.map Prod.fst = plan) (hσ1 : σ.map Prod.snd = plan)
    (a : Time) (ha : 0 < (a:ℝ)) (ha1 : (a:ℝ) < 1)
    (he : ∀ᵐ z ∂σ, z.1 a = z.2 a) :
    ∀ᵐ z ∂σ, dist (z.1 0) (z.1 1) = dist (z.2 0) (z.2 1) ∧
      dist (z.1 0) (z.2 1) = dist (z.1 0) (z.1 1) := by
  let A := fun z : C(Time,X) × C(Time,X) => dist (z.1 0) (z.1 1)
  let B := fun z : C(Time,X) × C(Time,X) => dist (z.2 0) (z.2 1)
  let c := fun z : C(Time,X) × C(Time,X) => dist (z.1 0) (z.2 1)
  let D := fun z => (a:ℝ)*A z^2+(1-(a:ℝ))*B z^2
  have hA : Integrable (fun z => A z^2) σ := by
    have h := hi
    rw [←hσ0] at h
    exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).mp h
  have hB : Integrable (fun z => B z^2) σ := by
    have h := hi
    rw [←hσ1] at h
    exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).mp h
  have hD : Integrable D σ := (hA.const_mul _).add (hB.const_mul _)
  have hg0 : ∀ᵐ z ∂σ, IsGeodesic z.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rwa [hσ0]
  have hg1 : ∀ᵐ z ∂σ, IsGeodesic z.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rwa [hσ1]
  have hbound : ∀ᵐ z ∂σ, c z ≤ (a:ℝ)*A z+(1-(a:ℝ))*B z := by
    filter_upwards [hg0,hg1,he] with z hz0 hz1 hz
    exact crossing_geodesic_distance_bound z.1 z.2 hz0 hz1 a hz
  have hle : ∀ᵐ z ∂σ, c z^2 ≤ D z := by
    filter_upwards [hbound] with z hz
    have hh := mul_self_le_mul_self (show 0 ≤ c z from dist_nonneg) hz
    have hn : 0 ≤ (a:ℝ)*(1-(a:ℝ))*(A z-B z)^2 :=
      mul_nonneg (mul_nonneg a.2.1 (sub_nonneg.mpr a.2.2)) (sq_nonneg _)
    dsimp [D]
    nlinarith only [hh,hn]
  have hc : Integrable (fun z => c z^2) σ := by
    apply hD.mono' (by dsimp [c]; fun_prop)
    filter_upwards [hle] with z hz
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (c z))] using hz
  have hIA : (∫ z, A z^2 ∂σ) = ∫ γ, dist (γ 0) (γ 1)^2 ∂plan := by
    rw [←hσ0,integral_map measurable_fst.aemeasurable (by fun_prop)]
  have hIB : (∫ z, B z^2 ∂σ) = ∫ γ, dist (γ 0) (γ 1)^2 ∂plan := by
    rw [←hσ1,integral_map measurable_snd.aemeasurable (by fun_prop)]
  have hID : (∫ z, D z ∂σ) = ∫ γ, dist (γ 0) (γ 1)^2 ∂plan := by
    rw [show D = fun z => (a:ℝ)*A z^2+(1-(a:ℝ))*B z^2 from rfl,
      integral_add (hA.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul,hIA,hIB]
    ring
  let κ := σ.map (fun z => (z.1 0,z.2 1))
  have hm : Measurable (fun z : C(Time,X) × C(Time,X) => (z.1 0,z.2 1)) :=
    ((measurable_path_eval (X := X) 0).comp measurable_fst).prodMk
    ((measurable_path_eval (X := X) 1).comp measurable_snd)
  have hends := optimalPlan_endpoints ν₀ ν₁ plan hp
  have hκ0 : κ.map Prod.fst = ν₀ := by
    dsimp only [κ]
    rw [Measure.map_map measurable_fst hm]
    rw [←hends.1,←hσ0,Measure.map_map (measurable_path_eval (X := X) 0) measurable_fst]
    rfl
  have hκ1 : κ.map Prod.snd = ν₁ := by
    dsimp only [κ]
    rw [Measure.map_map measurable_snd hm]
    rw [←hends.2,←hσ1,Measure.map_map (measurable_path_eval (X := X) 1) measurable_snd]
    rfl
  have hcost := hp.2.2 κ hκ0 hκ1
  dsimp only [κ] at hcost
  rw [transportCost_plan_eq_integral plan hi,
    transportCost_map_pair σ (fun z => z.1 0) (fun z => z.2 1) (by fun_prop) (by fun_prop) hc] at hcost
  have hge : (∫ z, D z ∂σ) ≤ ∫ z, c z^2 ∂σ := by
    rw [hID]
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)).mp hcost
  have heq : (fun z => c z^2) =ᵐ[σ] D :=
    (integral_eq_iff_of_ae_le hc hD hle).mp (le_antisymm (integral_mono_ae hc hD hle) hge)
  filter_upwards [hbound,heq] with z hb heq
  exact weighted_square_equality ha ha1 dist_nonneg dist_nonneg dist_nonneg hb heq


 
def reverseTime : C(Time,Time) :=
  ⟨fun t => ⟨1-(t:ℝ),sub_nonneg.mpr t.2.2,by linarith [t.2.1]⟩,by fun_prop⟩
@[simp] lemma reverseTime_coe (t : Time) : (reverseTime t : ℝ) = 1-(t:ℝ) := rfl
@[simp] lemma reverseTime_zero : reverseTime 0 = 1 := by ext; norm_num
@[simp] lemma reverseTime_one : reverseTime 1 = 0 := by ext; norm_num
@[simp] lemma reverseTime_reverseTime (t : Time) : reverseTime (reverseTime t) = t := by
  ext; simp

def reversePath (γ : C(Time,X)) : C(Time,X) := γ.comp reverseTime
omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma reversePath_apply (γ : C(Time,X)) (t : Time) :
    reversePath γ t = γ (reverseTime t) := rfl
omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma reversePath_reversePath (γ : C(Time,X)) : reversePath (reversePath γ) = γ := by
  ext t; simp

lemma measurable_reversePath [CompleteSpace X] [SeparableSpace X] :
    Measurable (reversePath (X := X)) := by
  apply measurable_path_of_eval
  intro t
  exact measurable_path_eval (reverseTime t)

omit [MeasurableSpace X] [BorelSpace X] in
lemma isGeodesic_reversePath (γ : C(Time,X)) (hγ : IsGeodesic γ) :
    IsGeodesic (reversePath γ) := by
  intro s t
  simp only [reversePath_apply,reverseTime_zero,reverseTime_one]
  rw [hγ (reverseTime s) (reverseTime t)]
  simp only [reverseTime_coe]
  rw [dist_comm (γ 1) (γ 0)]
  congr 1
  rw [show 1-(s:ℝ)-(1-(t:ℝ)) = (t:ℝ)-(s:ℝ) by ring,abs_sub_comm]

lemma IsOptimalCoupling.swap [SeparableSpace X] {ν₀ ν₁ : Measure X} {π : Measure (X×X)}
    (hp : IsOptimalCoupling ν₀ ν₁ π) : IsOptimalCoupling ν₁ ν₀ (π.map Prod.swap) := by
  refine ⟨?_,?_,?_⟩
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact hp.2.1
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact hp.1
  · intro κ hk0 hk1
    have h0 : (κ.map Prod.swap).map Prod.fst = ν₀ := by
      rw [Measure.map_map measurable_fst measurable_swap]; exact hk1
    have h1 : (κ.map Prod.swap).map Prod.snd = ν₁ := by
      rw [Measure.map_map measurable_snd measurable_swap]; exact hk0
    have hh := hp.2.2 (κ.map Prod.swap) h0 h1
    simpa only [transportCost_swap] using hh

lemma reversePlan_eval [CompleteSpace X] [SeparableSpace X]
    (plan : Measure C(Time,X)) (t : Time) :
    (plan.map reversePath).map (fun γ => γ t) = plan.map (fun γ => γ (reverseTime t)) := by
  rw [Measure.map_map (measurable_path_eval t) measurable_reversePath]
  rfl

lemma reversePlan_optimal [CompleteSpace X] [SeparableSpace X]
    (ν₀ ν₁ : Measure X) (plan : Measure C(Time,X))
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1)))) :
    IsOptimalCoupling ν₁ ν₀ ((plan.map reversePath).map (fun γ => (γ 0,γ 1))) := by
  have he : (plan.map reversePath).map (fun γ => (γ 0,γ 1)) =
      (plan.map (fun γ => (γ 0,γ 1))).map Prod.swap := by
    rw [Measure.map_map ((measurable_path_eval (X := X) 0).prodMk (measurable_path_eval (X := X) 1))
      measurable_reversePath,Measure.map_map measurable_swap
        ((measurable_path_eval (X := X) 0).prodMk (measurable_path_eval (X := X) 1))]
    congr 1
    funext γ
    simp
  rw [he]
  exact hp.swap

omit [BorelSpace X] in
lemma IsOptimalCoupling.mixture [SeparableSpace X] {ν₀ ν₁ : Measure X}
    {π κ : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    (hq : IsOptimalCoupling ν₀ ν₁ κ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsOptimalCoupling ν₀ ν₁ (measureMixture t π κ) := by
  have he : transportCost κ = transportCost π :=
    (wassersteinSq_eq_cost hq).symm.trans (wassersteinSq_eq_cost hp)
  have hc : transportCost (measureMixture t π κ) = transportCost π := by
    rw [transportCost_mixture,he,←add_mul,←ENNReal.ofReal_add (sub_nonneg.mpr ht1) ht]
    simp
  refine ⟨?_,?_,?_⟩
  · rw [measureMixture_map _ _ _ measurable_fst,hp.1,hq.1,measureMixture_self _ ht ht1]
  · rw [measureMixture_map _ _ _ measurable_snd,hp.2.1,hq.2.1,measureMixture_self _ ht ht1]
  · intro κ' h0 h1
    rw [hc]
    exact hp.2.2 κ' h0 h1

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma crossing_spliced_plan [SeparableSpace X] [CompleteSpace X]
    (ν₀ ν₁ : Measure X) (plan : Measure C(Time,X))
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) plan)
    (σ : Measure (C(Time,X) × C(Time,X)))
    (hσ0 : σ.map Prod.fst = plan) (hσ1 : σ.map Prod.snd = plan)
    (a : Time) (ha : 0 < (a:ℝ)) (ha1 : (a:ℝ) < 1)
    (he : ∀ᵐ z ∂σ, z.1 a = z.2 a) :
    let Q := σ.map (crossingSplice a)
    (∀ t : Time, Q.map (fun γ => γ t) = plan.map (fun γ => γ t)) ∧
    (∀ᵐ γ ∂Q, IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ (Q.map (fun γ => (γ 0,γ 1))) := by
  let f := crossingSplice (X := X) a
  have hf : Measurable f := measurable_crossingSplice a
  let Q := σ.map f
  change (∀ t : Time, Q.map (fun γ => γ t) = plan.map (fun γ => γ t)) ∧ _
  have heval (t : Time) : Q.map (fun γ => γ t) = plan.map (fun γ => γ t) := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_path_eval t) hf]
    by_cases hta : t ≤ a
    · rw [←hσ0,Measure.map_map (measurable_path_eval t) measurable_fst]
      apply Measure.map_congr
      filter_upwards [he] with z hz
      exact (crossingSplice_apply a z hz t).trans (ite_eq_left hta)
    · rw [←hσ1,Measure.map_map (measurable_path_eval t) measurable_snd]
      apply Measure.map_congr
      filter_upwards [he] with z hz
      exact (crossingSplice_apply a z hz t).trans (ite_eq_right hta)
  have hg0 : ∀ᵐ z ∂σ, IsGeodesic z.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable; rwa [hσ0]
  have hg1 : ∀ᵐ z ∂σ, IsGeodesic z.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable; rwa [hσ1]
  have hl := crossing_optimal_lengths ν₀ ν₁ plan hg hp hi σ hσ0 hσ1 a ha ha1 he
  have hfg : ∀ᵐ z ∂σ, IsGeodesic (f z) := by
    filter_upwards [he,hg0,hg1,hl] with z hz hz0 hz1 hzl
    dsimp only [f,crossingSplice]
    rw [dite_eq_left hz]
    exact isGeodesic_spliceAt_of_cross_length z.1 z.2 hz0 hz1 hzl.1 hzl.2 a hz
  refine ⟨heval,(ae_map_iff hf.aemeasurable isClosed_geodesicSet.measurableSet).mpr hfg,?_⟩
  have hA : Integrable (fun z : C(Time,X) × C(Time,X) => dist (z.1 0) (z.1 1)^2) σ := by
    have hh := hi
    rw [←hσ0] at hh
    exact hh.comp_measurable measurable_fst
  have hlen : (fun z => dist (f z 0) (f z 1)^2) =ᵐ[σ]
      (fun z => dist (z.1 0) (z.1 1)^2) := by
    filter_upwards [he,hl] with z hz hzl
    dsimp only [f,crossingSplice]
    rw [dite_eq_left hz,spliceAt_zero,spliceAt_one,hzl.2]
  have hif := hA.congr hlen.symm
  have hpair := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  have hcost : transportCost (Q.map (fun γ => (γ 0,γ 1))) =
      transportCost (plan.map (fun γ => (γ 0,γ 1))) := by
    dsimp only [Q]
    rw [Measure.map_map hpair hf]
    simp only [Function.comp_def]
    rw [transportCost_map_pair σ (fun z => f z 0) (fun z => f z 1)
      ((measurable_path_eval 0).comp hf) ((measurable_path_eval 1).comp hf) hif,transportCost_plan_eq_integral plan hi]
    congr 1
    rw [integral_congr_ae hlen,←hσ0,integral_map measurable_fst.aemeasurable (by fun_prop)]
  have hends := optimalPlan_endpoints ν₀ ν₁ plan hp
  refine ⟨?_,?_,?_⟩
  · rw [Measure.map_map measurable_fst hpair]
    exact (heval 0).trans hends.1
  · rw [Measure.map_map measurable_snd hpair]
    exact (heval 1).trans hends.2
  · intro κ hk0 hk1
    rw [hcost]
    exact hp.2.2 κ hk0 hk1

theorem NoncollapsedRCD.crossing_paths_agree_future
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
    ∀ᵐ z ∂σ, ∀ t : Time, a ≤ t → z.1 t = z.2 t := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : ProperSpace X := hX.proper K n hn
  have hi := optimalPlan_dist_sq_integrable ν₀ ν₁ plan hp p
    ((finiteSecondMoment_of_ae_dist_le ν₀ p hs0).integrable_dist_sq p)
    ((finiteSecondMoment_of_ae_dist_le ν₁ p hs1).integrable_dist_sq p)
  let f := crossingSplice (X := X) a
  have hf : Measurable f := measurable_crossingSplice a
  let Q := σ.map f
  have hQ := crossing_spliced_plan ν₀ ν₁ plan hg hp hi σ hσ0 hσ1 a ha ha1 hagree
  let : IsProbabilityMeasure Q := inferInstance
  let M := measureMixture (1/2) plan Q
  let : IsProbabilityMeasure M := measureMixture_probability (by norm_num) (by norm_num)
  have hMg : ∀ᵐ γ ∂M, IsGeodesic γ := ae_add_measure_iff.mpr
    ⟨hg.filter_mono Measure.smul_absolutelyContinuous.ae_le,
      hQ.2.1.filter_mono Measure.smul_absolutelyContinuous.ae_le⟩
  have hMp : IsOptimalCoupling ν₀ ν₁ (M.map (fun γ => (γ 0,γ 1))) := by
    dsimp only [M]
    rw [measureMixture_map _ _ _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    exact hp.mixture hQ.2.2 (by norm_num) (by norm_num)
  have hMc (t : Time) : M.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X := by
    dsimp only [M]
    rw [measureMixture_map _ _ _ (measurable_path_eval t),hQ.1 t,
      measureMixture_self _ (by norm_num) (by norm_num)]
    exact hcomp t
  let pair := fun z : C(Time,X) × C(Time,X) => (z.1,f z)
  have hpair : Measurable pair := measurable_fst.prodMk hf
  let τ := ENNReal.ofReal (1/2:ℝ) • σ.map pair
  have hτ0 : τ.map Prod.fst ≤ M := by
    dsimp only [τ,M]
    rw [Measure.map_smul _ measurable_fst.aemeasurable,Measure.map_map measurable_fst hpair]
    change ENNReal.ofReal (1/2:ℝ) • σ.map Prod.fst ≤ _
    rw [hσ0]
    dsimp only [measureMixture]
    norm_num only [show (1-(1/2:ℝ))=1/2 by norm_num]
    exact le_add_of_nonneg_right bot_le
  have hτ1 : τ.map Prod.snd ≤ M := by
    dsimp only [τ,M]
    rw [Measure.map_smul _ measurable_snd.aemeasurable,Measure.map_map measurable_snd hpair]
    change ENNReal.ofReal (1/2:ℝ) • Q ≤ _
    exact le_add_of_nonneg_left bot_le
  have hτag : ∀ᵐ z ∂τ, ∀ t : Time, t ≤ a → z.1 t = z.2 t := by
    apply Eventually.filter_mono Measure.smul_absolutelyContinuous.ae_le
    have hh : ∀ᵐ z ∂σ, ∀ t : Time, t ≤ a → (pair z).1 t = (pair z).2 t := by
      filter_upwards [hagree] with z hz
      intro t ht
      exact ((crossingSplice_apply a z hz t).trans (ite_eq_left ht)).symm
    apply (ae_map_iff hpair.aemeasurable ?_).mpr hh
    simpa only [Set.ofPred_forall] using (isClosed_iInter fun t : Time => isClosed_iInter fun _ : t ≤ a =>
      (isClosed_eq (by fun_prop) (by fun_prop) :
        IsClosed {z : C(Time,X) × C(Time,X) | z.1 t = z.2 t})).measurableSet
  have hno := hX.compressed_optimal_plan_no_interior_branching K n hn ν₀ ν₁ p hR hs0 hs1
    M hMg hMp C hMc τ hτ0 hτ1 a ha hτag
  have hno' : ∀ᵐ z ∂σ.map pair, z.1 = z.2 :=
    hno.filter_mono (Measure.absolutelyContinuous_smul
      (by norm_num : ENNReal.ofReal (1/2:ℝ) ≠ 0)).ae_le
  have hpull := ae_of_ae_map hpair.aemeasurable hno'
  filter_upwards [hagree,hpull] with z hz hpz
  intro t ht
  by_cases hta : t ≤ a
  · have heq : t = a := le_antisymm hta ht
    simpa only [heq] using hz
  · have hfunc : z.1 = f z := hpz
    rw [hfunc]
    exact (crossingSplice_apply a z hz t).trans (ite_eq_right hta)


end RegularPointCoordinates

end OAI
