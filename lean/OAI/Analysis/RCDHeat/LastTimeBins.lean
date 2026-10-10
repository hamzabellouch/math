import Mathlib
import OAI.Analysis.RCDHeat.EntropyPlanExtension
import OAI.Analysis.RCDHeat.ForkPlans

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: LastTimeBins, LogBinLimit, NoBranchAtTime, AePathEquality, Nonbranching. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory
open scoped ENNReal

lemma exists_uniform_time_bin {A : Type*} [MeasurableSpace A]
    (σ : Measure A) [IsFiniteMeasure σ] (T : A → ℝ) {l r : ℝ} (hlr : l < r)
    (hT : ∀ᵐ z ∂σ, l ≤ T z ∧ T z < r) (N : ℕ) (hN : 0 < N) :
    ∃ i : Fin N, (σ univ).toReal/(N:ℝ) ≤
      (σ {z | l+(i:ℝ)*((r-l)/(N:ℝ)) ≤ T z ∧
        T z < l+((i:ℝ)+1)*((r-l)/(N:ℝ))}).toReal := by
  classical
  let B := fun i : Fin N => {z | l+(i:ℝ)*((r-l)/(N:ℝ)) ≤ T z ∧
    T z < l+((i:ℝ)+1)*((r-l)/(N:ℝ))}
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hd : 0 < (r-l)/(N:ℝ) := div_pos (sub_pos.mpr hlr) hNr
  have hcov : ∀ᵐ z ∂σ, z ∈ ⋃ i, B i := by
    filter_upwards [hT] with z hz
    let y := (T z-l)/((r-l)/(N:ℝ))
    have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hz.1) hd.le
    have hyN : y < (N:ℝ) := by
      apply (div_lt_iff₀ hd).mpr
      rw [mul_div_cancel₀ _ hNr.ne']
      linarith only [hz.2]
    let i : Fin N := ⟨⌊y⌋₊,(Nat.floor_lt hy0).mpr hyN⟩
    apply mem_iUnion.mpr
    refine ⟨i,?_,?_⟩
    · have hlow := (Nat.floor_le hy0)
      have hh := (le_div_iff₀ hd).mp hlow
      change l+(⌊y⌋₊:ℝ)*((r-l)/(N:ℝ)) ≤ T z
      linarith only [hh]
    · have hu := Nat.lt_floor_add_one y
      have hh := (div_lt_iff₀ hd).mp hu
      change T z < l+((⌊y⌋₊:ℝ)+1)*((r-l)/(N:ℝ))
      nlinarith only [hh]
  have hsum : σ univ ≤ ∑ i : Fin N, σ (B i) := by
    have hc : σ univ ≤ σ (⋃ i, B i) := by
      apply measure_mono_ae
      filter_upwards [hcov] with z hz
      exact fun _ => hz
    exact hc.trans (by simpa only [tsum_fintype] using measure_iUnion_le B)
  have hreal : (σ univ).toReal ≤ ∑ i : Fin N, (σ (B i)).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => measure_ne_top σ (B i))) hsum
    simpa only [ENNReal.toReal_sum (fun i _ => measure_ne_top σ (B i))] using hh
  have hnonempty : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  have hsum' : (∑ _i : Fin N, (σ univ).toReal/(N:ℝ)) ≤ ∑ i : Fin N, (σ (B i)).toReal := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      mul_div_cancel₀ _ hNr.ne'] using hreal
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le hnonempty hsum'
  exact ⟨i,hi⟩

end

 
section

 

open Filter
open scoped Topology

lemma tendsto_log_bin_budget (q δ V W w : ℝ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => 2*((Real.log (q*(N:ℝ))+V)/δ+W)*(w/(N:ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero,Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hconst (c : ℝ) : Tendsto (fun N : ℕ => c/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := ((hconst (Real.log q)).add hlog).const_mul (2*(w/δ))
  have hh' := hh.add ((hconst w).const_mul (2*(V/δ+W)))
  simp only [add_zero,mul_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hNr : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  rw [Real.log_mul hq.ne' hNr]
  ring

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma normalized_cut_density_bound {M m C N : ℝ} (hM : 0 < M) (hm : 0 < m)
    (hC : 0 < C) (hN : 0 < N) (h : M/N/16 ≤ m) :
    m⁻¹*(2*C) ≤ (32*C/M)*N := by
  have hh : M ≤ m*(16*N) := by
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ)<16)).mp h
    have h'' := (div_le_iff₀ hN).mp h'
    nlinarith only [h'']
  have hinv : m⁻¹ ≤ (16*N)/M := by
    rw [inv_eq_one_div,div_le_div_iff₀ hm hM]
    nlinarith only [hh]
  calc
    _ ≤ ((16*N)/M)*(2*C) := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = _ := by ring

 

theorem NoncollapsedRCD.coupled_branch_mass_zero
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ u : Time,
      plan.map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ u : Time, ∀ᵐ x ∂plan.map (fun γ => γ u), dist x p ≤ R)
    (σ : Measure (C(Time,X) × C(Time,X))) [IsFiniteMeasure σ]
    (hσ0 : σ.map Prod.fst ≤ plan) (hσ1 : σ.map Prod.snd ≤ plan)
    (a b : Time) (ha : 0 < (a:ℝ)) (hab : a < b) (hb : (b:ℝ) < 1)
    (hagree : ∀ᵐ z ∂σ, ∀ t : Time, t ≤ a → z.1 t = z.2 t)
    (hsep : ∀ᵐ z ∂σ, z.1 b ≠ z.2 b) : σ univ = 0 := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  by_contra hne
  let M := (σ univ).toReal
  have hM : 0 < M := ENNReal.toReal_pos hne (measure_ne_top σ univ)
  let δ := min (a:ℝ) (1-(b:ℝ))
  have hδ : 0 < δ := lt_min ha (by linarith)
  let w := (b:ℝ)-(a:ℝ)
  have hw : 0 < w := sub_pos.mpr hab
  let q := 32*C/M
  have hq : 0 < q := div_pos (mul_pos (by norm_num) hC) hM
  let V := 2*(hausdorff n X (closedBall p R)).toReal+4*|K| *R^2
  let W := 4*|K| *R^2
  have hlim := tendsto_log_bin_budget q δ V W w hq
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2*((Real.log (q*(N:ℝ))+V)/δ+W)*(w/(N:ℝ)) < Real.log 2 :=
    hlim.eventually (gt_mem_nhds (Real.log_pos (by norm_num)))
  obtain ⟨N,hN,hsmallN⟩ := ((eventually_gt_atTop (0:ℕ)).and hsmall).exists
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let d := w/(N:ℝ)
  have hd : 0 < d := div_pos hw hNr
  have hg0 : ∀ᵐ z ∂σ, IsGeodesic z.1 := by
    exact ae_of_ae_map measurable_fst.aemeasurable (hg.filter_mono (ae_mono hσ0))
  have hg1 : ∀ᵐ z ∂σ, IsGeodesic z.2 := by
    exact ae_of_ae_map measurable_snd.aemeasurable (hg.filter_mono (ae_mono hσ1))
  let f := lastMeetingSplice (X := X) b
  have hf : Measurable f := measurable_lastMeetingSplice b
  have hfp : ∀ᵐ z ∂σ, IsGeodesic (f z) ∧ f z 0 = z.1 0 ∧ f z 1 = z.2 1 ∧
      (∀ t : Time, t ≤ lastMeeting b z → f z t = z.1 t) ∧
      (∀ t : Time, lastMeeting b z < t → t ≤ b → f z t ≠ z.1 t) := by
    filter_upwards [hg0,hg1,hagree] with z h0 h1 hag
    exact lastMeetingSplice_properties b z h0 h1 a ha hag
  have hT : ∀ᵐ z ∂σ, (a:ℝ) ≤ (lastMeeting b z:ℝ) ∧ (lastMeeting b z:ℝ) < (b:ℝ) := by
    filter_upwards [hagree,hsep] with z hag hneq
    refine ⟨le_lastMeeting b z hab.le (hag a le_rfl),?_⟩
    apply lt_of_le_of_ne (lastMeeting_le b z)
    intro he
    have hh := lastMeeting_eq b z (hag 0 a.2.1)
    exact hneq (by simpa only [he] using hh)
  obtain ⟨i,hi⟩ := exists_uniform_time_bin σ (fun z => (lastMeeting b z:ℝ)) hab hT N hN
  let sR := (a:ℝ)+(i:ℝ)*d
  let tR := (a:ℝ)+((i:ℝ)+1)*d
  have has : (a:ℝ) ≤ sR := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i.val) hd.le)
  have hstR : sR ≤ tR := by dsimp [sR,tR]; nlinarith only [hd]
  have htb : tR ≤ (b:ℝ) := by
    have hiN : (i:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast i.isLt
    have hmul := mul_le_mul_of_nonneg_right hiN hd.le
    dsimp only [tR,d,w]
    rw [mul_div_cancel₀ _ hNr.ne'] at hmul
    linarith only [hmul]
  let s : Time := ⟨sR,⟨a.2.1.trans has,(hstR.trans htb).trans b.2.2⟩⟩
  let t : Time := ⟨tR,⟨a.2.1.trans (has.trans hstR),htb.trans b.2.2⟩⟩
  let B := {z : C(Time,X) × C(Time,X) | sR ≤ (lastMeeting b z:ℝ) ∧ (lastMeeting b z:ℝ) < tR}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const ((measurable_lastMeeting b).subtype_val)).inter
      (measurableSet_lt ((measurable_lastMeeting b).subtype_val) measurable_const)
  let β := σ.restrict B
  have hβ : β ≤ σ := Measure.restrict_le_self
  have hβmem : ∀ᵐ z ∂β, s ≤ lastMeeting b z ∧ lastMeeting b z < t := ae_restrict_mem hB
  have hβne : ∀ᵐ z ∂β, z.1 t ≠ f z t := by
    filter_upwards [hβmem,hfp.filter_mono (ae_mono hβ)] with z hz hprop
    exact (hprop.2.2.2.2 t hz.2 htb).symm
  obtain ⟨S,hS,hcut⟩ := exists_measurable_directed_cut β (fun z => z.1 t) (fun z => f z t)
    ((measurable_path_eval t).comp measurable_fst) ((measurable_path_eval t).comp hf)
  have hall : β univ ≤ β {z | z.1 t ≠ f z t} :=
    measure_mono_ae (hβne.mono fun z hz _ => hz)
  have hcu := (ENNReal.div_le_div_right hall 16).trans hcut
  let D := {z | z.1 t ∈ S ∧ f z t ∉ S}
  have hD : MeasurableSet D :=
    (hS.preimage ((measurable_path_eval t).comp measurable_fst)).inter
      (hS.compl.preimage ((measurable_path_eval t).comp hf))
  let τ := β.restrict D
  have hτβ : τ ≤ β := Measure.restrict_le_self
  have hτσ : τ ≤ σ := hτβ.trans hβ
  have hmass : M/(N:ℝ)/16 ≤ (τ univ).toReal := by
    have hh := ENNReal.toReal_mono (measure_ne_top β D) hcu
    rw [ENNReal.toReal_div,ENNReal.toReal_ofNat] at hh
    change (β univ).toReal/16 ≤ (β D).toReal at hh
    rw [show β univ = σ B from Measure.restrict_apply_univ B] at hh
    have hi' : M/(N:ℝ) ≤ (σ B).toReal := hi
    exact (div_le_div_of_nonneg_right hi' (by norm_num)).trans (by simpa [τ] using hh)
  have hm : 0 < (τ univ).toReal := lt_of_lt_of_le (div_pos (div_pos hM hNr) (by norm_num)) hmass
  have hτne : τ univ ≠ 0 := by intro hh; simp only [hh,ENNReal.toReal_zero,lt_self_iff_false] at hm
  have hlog : Real.log ((τ univ)⁻¹.toReal*(2*C)) ≤ Real.log (q*(N:ℝ)) := by
    apply Real.log_le_log
    · rw [ENNReal.toReal_inv]
      exact mul_pos (inv_pos.mpr hm) (mul_pos (by norm_num) hC)
    · rw [ENNReal.toReal_inv]
      exact normalized_cut_density_bound hM hm hC hNr hmass
  have hfork := hX.entropy_coupled_fork_gap K n hn plan hg hp hC hc p hR hs τ hτne
    ((Measure.map_mono hτσ measurable_fst).trans hσ0)
    ((Measure.map_mono hτσ measurable_snd).trans hσ1) f hf
    ((hfp.filter_mono (ae_mono hτσ)).mono fun z hz => hz.1)
    (by
      filter_upwards [hfp.filter_mono (ae_mono hτσ),hagree.filter_mono (ae_mono hτσ)] with z hz hag
      exact ⟨hz.2.1,hz.2.2.1,hag 0 a.2.1⟩)
    (by
      intro u
      filter_upwards [hagree.filter_mono (ae_mono hτσ)] with z hag
      classical
      have h0 := hag 0 a.2.1
      dsimp only [f,lastMeetingSplice]
      rw [dite_eq_left h0,spliceAt_apply]
      split_ifs <;> simp)
    hδ s t ((min_le_left _ _).trans has) hstR
    (by have hh := min_le_right (a:ℝ) (1-(b:ℝ)); dsimp only [δ]; linarith only [htb,hh])
    (by
      filter_upwards [hβmem.filter_mono (ae_mono hτβ),hfp.filter_mono (ae_mono hτσ)] with z hz hprop
      exact (hprop.2.2.2.1 s hz.1).symm)
    S hS (ae_restrict_mem hD)
  have hwidth : (t:ℝ)-(s:ℝ) = w/(N:ℝ) := by dsimp [s,t,sR,tR,d]; ring
  rw [hwidth] at hfork
  have hbound : Real.log 2 ≤ 2*((Real.log (q*(N:ℝ))+V)/δ+W)*(w/(N:ℝ)) := by
    apply hfork.trans
    dsimp only [V,W]
    rw [←mul_assoc]
    simp only [←add_assoc]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hw.le hNr.le)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ hδ.le
    linarith only [hlog]
  exact (not_lt_of_ge hbound) hsmallN

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
lemma ae_path_eq_of_ae_eval_lt_one (σ : Measure (C(Time,X) × C(Time,X)))
    (he : ∀ t : Time, (t:ℝ) < 1 → ∀ᵐ z ∂σ, z.1 t = z.2 t) :
    ∀ᵐ z ∂σ, z.1 = z.2 := by
  let b : ℕ → Time := fun k => ⟨1-1/((k:ℝ)+1),by
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    constructor
    · have hh : 1/((k:ℝ)+1) ≤ 1 := (div_le_one hk).mpr (by have hh : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      linarith
    · have hh : 0 ≤ 1/((k:ℝ)+1) := by positivity
      linarith⟩
  have hb (k : ℕ) : (b k:ℝ) < 1 := by
    have hh : 0 < 1/((k:ℝ)+1) := by positivity
    change 1-1/((k:ℝ)+1) < 1
    linarith only [hh]
  have hlim : Tendsto b atTop (𝓝 (1:Time)) := by
    apply tendsto_subtype_rng.mpr
    have hh := (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0))
    simpa only [b,sub_zero,show ((1:Time):ℝ)=1 from rfl] using hh
  have h1 : ∀ᵐ z ∂σ, z.1 1 = z.2 1 := by
    have hh : ∀ᵐ z ∂σ, ∀ k : ℕ, z.1 (b k) = z.2 (b k) := ae_all_iff.mpr (fun k => he (b k) (hb k))
    filter_upwards [hh] with z hz
    apply tendsto_nhds_unique ((z.1.continuous.tendsto 1).comp hlim)
    exact ((z.2.continuous.tendsto 1).comp hlim).congr (fun k => (hz k).symm)
  have hall (t : Time) : ∀ᵐ z ∂σ, z.1 t = z.2 t := by
    rcases lt_or_eq_of_le t.2.2 with ht | ht
    · exact he t ht
    · have ht' : t = 1 := Subtype.ext ht
      simpa only [ht'] using h1
  have hh : ∀ᵐ z ∂σ, ∀ q : ℚ, z.1 (rationalTime q) = z.2 (rationalTime q) :=
    ae_all_iff.mpr (fun q => hall (rationalTime q))
  filter_upwards [hh] with z hz
  apply ContinuousMap.ext
  have hh := rationalTime_dense.equalizer z.1.continuous z.2.continuous (funext hz)
  exact congrFun hh

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem NoncollapsedRCD.compressed_optimal_plan_no_interior_branching
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hcomp : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (σ : Measure (C(Time,X) × C(Time,X)))
    (hσ0 : σ.map Prod.fst ≤ plan) (hσ1 : σ.map Prod.snd ≤ plan)
    (a : Time) (ha : 0 < (a:ℝ))
    (hagree : ∀ᵐ z ∂σ, ∀ t : Time, t ≤ a → z.1 t = z.2 t) :
    ∀ᵐ z ∂σ, z.1 = z.2 := by
  let : SeparableSpace X := hX.separable
  let : IsFiniteMeasure (σ.map Prod.fst) := isFiniteMeasure_of_le plan hσ0
  let : IsFiniteMeasure σ := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  let C' := (C:ℝ)+1
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hcomp' (t : Time) : plan.map (fun γ => γ t) ≤ ENNReal.ofReal C' • hausdorff n X := by
    apply (hcomp t).trans
    apply Measure.le_iff.mpr
    intro S hS
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
    dsimp [C']
    linarith
  have he := optimalPlan_endpoints ν₀ ν₁ plan hp
  have hp' : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
  have hs (t : Time) : ∀ᵐ x ∂plan.map (fun γ => γ t), dist x p ≤ 3*R := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ plan hg hp p hR hs0 hs1).mono fun γ hz => hz.2 t
  apply ae_path_eq_of_ae_eval_lt_one σ
  intro b hb
  by_cases hba : b ≤ a
  · exact hagree.mono fun z hz => hz b hba
  · have hab : a < b := lt_of_not_ge hba
    let E := {z : C(Time,X) × C(Time,X) | z.1 b ≠ z.2 b}
    have hE : MeasurableSet E := (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet.compl
    have hh := hX.coupled_branch_mass_zero K n hn plan hg hp' hC' hcomp' p
      (mul_nonneg (by norm_num) hR) hs (σ.restrict E)
      ((Measure.map_mono Measure.restrict_le_self measurable_fst).trans hσ0)
      ((Measure.map_mono Measure.restrict_le_self measurable_snd).trans hσ1) a b ha hab hb
      (hagree.filter_mono (ae_mono Measure.restrict_le_self)) (ae_restrict_mem hE)
    rw [Measure.restrict_apply_univ] at hh
    exact ae_iff.mpr hh


end RegularPointCoordinates

end OAI
