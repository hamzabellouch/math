import Mathlib
import OAI.Probability.SKFluctuations.ScalarFlattenCurvature

namespace OAI

/-! Scalar Full Origin Marginality. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_zero_head_obstruction {T q : ℝ} (hT : 1 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β)
    (hR : ∀ s ∈ Ioo (0:ℝ) q, 1 < scalarHeadObservedRatio (zero_lt_one.trans hT) α s 0) :
    False := by
  have hap (s : ℝ) (hs : 0 < s) : 0 < α.val s :=
    (α.property.1 0).1.trans_lt (scalarMinimizer_strict_origin hT α hα hmin hs)
  have hv := scalarMinimizer_zero_head_variation (zero_lt_one.trans hT) hq α hα (hap q hq.1) hc hmin
  let f : ℝ → ℝ := fun s => α.val s*s*(scalarHeadObservedRatio (zero_lt_one.trans hT) α s 0-1)
  have hi : IntervalIntegrable f volume 0 q := by
    convert (scalarHeadVariation_integrable (zero_lt_one.trans hT) α 0 0 q).neg using 1
    funext s
    dsimp [f]
    ring
  have hp : 0 < ∫ s in (0:ℝ)..q, f s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hi (fun s hs =>
      mul_pos (mul_pos (hap s hs.1) hs.1) (sub_pos.mpr (hR s hs))) hq.1
  have he : (fun s => -α.val s*s*(scalarHeadObservedRatio (zero_lt_one.trans hT) α s 0-1)) =
      fun s => -f s := by
    funext s
    dsimp [f]
    ring
  rw [he,intervalIntegral.integral_neg] at hv
  linarith

 

theorem scalarMinimizer_origin_marginality {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    T*((scalarTailJet (zero_lt_one.trans hT) α 0).A₁ 0 0)^2 = 1 := by
  apply le_antisymm _ (scalarMinimizer_origin_curvature_ge hT α hα hc hmin)
  by_contra hn
  have hR : 1 < scalarHeadObservedRatio (zero_lt_one.trans hT) α 0 0 := by
    rw [scalarHeadObservedRatio_zero]
    exact lt_of_not_ge hn
  have hcR : Continuous (fun s => scalarHeadObservedRatio (zero_lt_one.trans hT) α s 0) :=
    (scalarHeadObservedRatio_continuous (zero_lt_one.trans hT) α).comp
      (f := fun s : ℝ => (s,0)) (continuous_id.prodMk continuous_const)
  obtain ⟨q,hq,hqR⟩ := exists_small_right_interval hcR hR
  exact scalarMinimizer_zero_head_obstruction hT hq α hα hc hmin hqR

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_origin_zero {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    α.val 0 = 0 := by
  by_contra hn
  have hm : 0 < α.val 0 := lt_of_le_of_ne (α.property.1 0).1 (Ne.symm hn)
  let hT0 : 0 < T := zero_lt_one.trans hT
  let H : ℝ → ℝ := fun q => (scalarTailJet hT0 α q).H 0 0
  let K : ℝ := -(T/2)*(scalarTailSpatialJet hT0 α 4 0 0+2*α.val 0*(H 0)^2)
  let R : ℝ × ℝ → ℝ := fun p =>
    T*(H p.1+H 0)*rightSlope H K p.1+scalarHeadSecondRate hT0 α p.1 p.2
  have hH : Continuous H := by
    have hz : Continuous (fun q : ℝ => (q,(0:Fin 1 → ℝ))) := by fun_prop
    exact Continuous.comp (g:=fun p : ℝ × (Fin 1 → ℝ) => (scalarTailJet hT0 α p.1).H 0 p.2)
      (f:=fun q : ℝ => (q,(0:Fin 1 → ℝ))) ((scalarTailJetFamily hT0 α).continuousH 0) hz
  have hd : HasDerivWithinAt H K (Ioi 0) 0 :=
    scalarTailJet_origin_curvature_hasDerivWithinAt hT0 α hm hc
  have hsc : ContinuousWithinAt (fun p : ℝ × ℝ => rightSlope H K p.1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) (0,α.val 0) :=
    (rightSlope_continuousWithinAt hd).comp (f:=fun p : ℝ × ℝ => p.1)
      (x:=(0,α.val 0)) continuous_fst.continuousWithinAt
      (fun _ hp => hp.1)
  have hR : ContinuousWithinAt R (Ioi 0 ×ˢ (univ : Set ℝ)) (0,α.val 0) :=
    ((((hH.comp continuous_fst).add continuous_const).const_mul T).continuousWithinAt.mul hsc).add
      (scalarHeadSecondRate_continuous hT0 α).continuousWithinAt
  have hp : 0 < H 0 := scalarProfileJet_curvature_pos (rescaledMassProfile α hT0)
    (fun s => (α.property.1 (s/T)).2) _ _ _
  have hR0 : R (0,α.val 0) < 0 := by
    have he : R (0,α.val 0) = -(T^2*α.val 0*(H 0)^3) := by
      dsimp only [R,Prod.fst,Prod.snd]
      rw [scalarHeadSecondRate_zero,unitMassClip_eq (α.property.1 0)]
      simp only [rightSlope,ite_true]
      change T*(H 0+H 0)*K+T^2*(H 0*scalarTailSpatialJet hT0 α 4 0 0+
        α.val 0*(H 0)^3) = _
      dsimp only [K]
      ring
    rw [he]
    exact neg_neg_of_pos (mul_pos (mul_pos (sq_pos_of_pos hT0) hm) (pow_pos hp 3))
  obtain ⟨q,hq,hqR⟩ := exists_small_upper_triangle_within hR (hc 0) hR0
  have hmar : T*(H 0)^2 = 1 := scalarMinimizer_origin_marginality hT α hα hc hmin
  apply scalarMinimizer_upper_head_obstruction hT hq α hα hc hmin
  intro s hs
  have he := scalarHeadObservedRatio_second_expansion hT0 α hs.1.le (α.property.1 q)
  have he' : scalarHeadObservedRatio hT0 α s (α.val q) = 1+s*R (s,α.val q) := by
    rw [he,← hmar]
    dsimp only [R,Prod.fst,Prod.snd,rightSlope]
    rw [ite_eq_right hs.1.ne']
    change T*(H s)^2+s*scalarHeadSecondRate hT0 α s (α.val q) =
      T*(H 0)^2+s*(T*(H s+H 0)*((H s-H 0)/s)+scalarHeadSecondRate hT0 α s (α.val q))
    field_simp [hs.1.ne']
    ring
  rw [he']
  linarith [mul_neg_of_pos_of_neg hs.1 (hqR s hs)]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_zero_mem_closure_support {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β) :
    (0:ℝ) ∈ closure ((profileStieltjes α).measure.support ∩ Ioi 0) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, hx, hs⟩ := Measure.nonempty_inter_support_of_pos
    (scalarMinimizer_origin_accumulates hT α hα hmin hε)
  exact ⟨x,⟨hs,hx.1⟩,by simpa only [Real.dist_eq,zero_sub,abs_neg,abs_of_pos hx.1] using hx.2⟩

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_measure_origin_zero {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    (profileStieltjes α).measure {(0:ℝ)} = 0 := by
  let β := rightMassProfile α
  have hβ : β ∈ scalarProfiles := rightMassProfile_mem hα
  have hc (s : ℝ) : ContinuousWithinAt β.val (Ici s) s :=
    continuousWithinAt_rightLim_Ici (α.property.2.tendsto_rightLim s)
  have hminβ : ∀ γ ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) β ≤
      scalarParisiValue (zero_lt_one.trans hT) γ := by
    intro γ hγ
    rw [scalarParisiValue_congr_ae (zero_lt_one.trans hT) (rightMassProfile_ae α)]
    exact hmin γ hγ
  have hz : profileStieltjes α 0 = 0 := scalarMinimizer_origin_zero hT β hβ hc hminβ
  rw [(profileStieltjes α).measure_singleton,profileStieltjes_left_zero hα,hz,sub_self,
    ENNReal.ofReal_zero]

 

theorem scalarParisiValue_attains_origin_regular {T : ℝ} (hT : 1 < T) :
    ∃ (α : boundedMassProfiles), α ∈ scalarProfiles ∧
      (∀ s, ContinuousWithinAt α.val (Ici s) s) ∧
      IsProbabilityMeasure (profileStieltjes α).measure ∧
      (∀ s, cdf (profileStieltjes α).measure s = α.val s) ∧
      (∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
        scalarParisiValue (zero_lt_one.trans hT) β) ∧
      α.val 0 = 0 ∧
      (profileStieltjes α).measure {(0:ℝ)} = 0 ∧
      T*((scalarTailJet (zero_lt_one.trans hT) α 0).A₁ 0 0)^2 = 1 ∧
      (∀ q : ℝ, 0 < q → 0 < (profileStieltjes α).measure (Ioo 0 q)) := by
  obtain ⟨α,hα,hc,hp,hcdf,hmin⟩ := scalarParisiValue_attains_distribution (zero_lt_one.trans hT)
  exact ⟨α,hα,hc,hp,hcdf,hmin,scalarMinimizer_origin_zero hT α hα hc hmin,
    scalarMinimizer_measure_origin_zero hT α hα hmin,
    scalarMinimizer_origin_marginality hT α hα hc hmin,
    fun _ hq => scalarMinimizer_origin_accumulates hT α hα hmin hq⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

theorem profileStieltjes_rightMass (α : boundedMassProfiles) :
    profileStieltjes (rightMassProfile α)=profileStieltjes α := by
  ext x
  exact rightLim_rightLim (α.property.2.tendsto_rightLim x)

theorem scalarProfile_constant_of_support_hole (α : boundedMassProfiles)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x) {p r : ℝ}
    (hs : ∀ u ∈ Ioo p r, u ∉ (profileStieltjes α).measure.support)
    {u v : ℝ} (hu : u ∈ Ioo p r) (hv : v ∈ Ioo p r) : α.val u=α.val v := by
  have hh (u v : ℝ) (hu : u ∈ Ioo p r) (hv : v ∈ Ioo p r) (huv : u ≤ v) :
      α.val u=α.val v := by
    have hz : (profileStieltjes α).measure (Ioc u v)=0 :=
      measure_mono_null (fun y hy => hs y ⟨hu.1.trans hy.1,hy.2.trans_lt hv.2⟩)
        Measure.measure_compl_support
    rw [(profileStieltjes α).measure_Ioc] at hz
    change ENNReal.ofReal (α.val.rightLim v-α.val.rightLim u)=0 at hz
    rw [(hc u).rightLim_eq,(hc v).rightLim_eq] at hz
    exact le_antisymm (α.property.2 huv) (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz))
  obtain huv | hvu := le_total u v
  · exact hh u v hu hv huv
  · exact (hh v u hv hu hvu).symm

theorem scalarMinimizer_support_interval {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) {a x b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hax : a < x) (hxb : x < b)
    (hsa : a ∈ (profileStieltjes α).measure.support)
    (hsb : b ∈ (profileStieltjes α).measure.support) :
    x ∈ (profileStieltjes α).measure.support := by
  by_contra hx
  obtain ⟨p,r,hsp,hsr,hap,hpx,hxr,hrb,hgap⟩ :=
    closedSet_gap_endpoints Measure.isClosed_support hsa hsb hax hxb hx
  let β := rightMassProfile α
  have hβ : β ∈ scalarProfiles := rightMassProfile_mem hα
  have hc (u : ℝ) : ContinuousWithinAt β.val (Ici u) u :=
    continuousWithinAt_rightLim_Ici (α.property.2.tendsto_rightLim u)
  have he : profileStieltjes β=profileStieltjes α := profileStieltjes_rightMass α
  have hminβ : ∀ γ ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) β ≤
      scalarParisiValue (zero_lt_one.trans hT) γ := by
    intro γ hγ
    rw [scalarParisiValue_congr_ae (zero_lt_one.trans hT) (rightMassProfile_ae α)]
    exact hmin γ hγ
  have hgapβ : ∀ u ∈ Ioo p r, u ∉ (profileStieltjes β).measure.support := by
    rwa [he]
  have hf (u : ℝ) (hu : u ∈ Ioo p r) : β.val u=β.val x :=
    scalarProfile_constant_of_support_hole β hc hgapβ hu ⟨hpx,hxr⟩
  exact scalarMinimizer_no_positive_support_gap hT (ha.trans_le hap) (hpx.trans hxr)
    (hrb.trans_lt hb) β hβ (fun u _ => hc u) hf (by rwa [he]) (by rwa [he]) hminβ

 

theorem scalarMinimizer_support_initial_interval {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 1)
    (hsq : q ∈ (profileStieltjes α).measure.support) :
    Icc 0 q ⊆ (profileStieltjes α).measure.support := by
  intro x hx
  obtain h0 | h0 := hx.1.eq_or_lt
  · subst x
    have hh := scalarMinimizer_zero_mem_closure_support hT α hα hmin
    exact Measure.isClosed_support.closure_subset_iff.mpr inter_subset_left hh
  obtain hq' | hq' := hx.2.eq_or_lt
  · simpa only [hq'] using hsq
  obtain ⟨u,hu,hsu⟩ := Measure.nonempty_inter_support_of_pos
    (scalarMinimizer_origin_accumulates hT α hα hmin h0)
  exact scalarMinimizer_support_interval hT α hα hmin hu.1 hq.2 hu.2 hq' hsu hsq

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarMinimizer_one_not_support_rc {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (1:ℝ) ∉ (profileStieltjes α).measure.support := by
  intro hs
  have ha1 : α.val 1=1 := by
    have hh := profileStieltjes_one hα
    change α.val.rightLim 1=1 at hh
    rwa [(hc 1).rightLim_eq] at hh
  have hm : 0 < α.val 1 := by rw [ha1]; norm_num
  let p : ℕ → ℝ := fun k => 1-1/((k:ℝ)+1)
  have hp0 (k : ℕ) : 0 ≤ p k := by
    dsimp only [p]
    have hh : (1:ℝ)/((k:ℝ)+1) ≤ 1 := by
      rw [div_le_iff₀ (show (0:ℝ)<(k:ℝ)+1 by positivity)]
      nlinarith [Nat.cast_nonneg (α:=ℝ) k]
    linarith
  have hp1 (k : ℕ) : p k < 1 := by
    dsimp only [p]
    have hh : (0:ℝ)<1/((k:ℝ)+1) := by positivity
    linarith
  have hp : Tendsto p atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    simpa only [sub_zero] using hh
  have hW (k : ℕ) : (∫ s in p k..1, α.val s-α.val 1)<0 := by
    have hu : α.val ((p k+1)/2)<α.val 1 := by
      have hh := profileStieltjes_support_strict α hs (by linarith [hp1 k] : (p k+1)/2<1)
        (by norm_num : (1:ℝ)<2)
      rw [hα.2 2 (by norm_num),ha1] at *
      exact hh
    exact scalarInterval_up_area_neg α (by linarith [hp1 k]) (by linarith [hp1 k]) hu
  have hl (k : ℕ) := scalarMinimizer_local_lower hT (hp0 k) (hp1 k) le_rfl α hα hmin hm (hW k)
  have he := scalarFlattenedEnergy_varying_mass_tendsto hT α (fun _ => α.val 1)
    (fun _ => hm) (fun _ => (α.property.1 1).2) hp tendsto_const_nhds (fun k => (hp1 k).le)
  have hd : Tendsto (fun k => p k-6*T*(1-p k)) atTop (𝓝 1) := by
    simpa only [sub_self,mul_zero,sub_zero] using hp.sub (((tendsto_const_nhds (x:=(1:ℝ))).sub hp).const_mul (6*T))
  have hge := le_of_tendsto_of_tendsto' hd he hl
  exact (not_lt_of_ge hge) (scalarPlantedEnergy_lt_one hT α zero_lt_one le_rfl hm (fun x _ => hc x))

theorem scalarMinimizer_one_not_support {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (1:ℝ) ∉ (profileStieltjes α).measure.support := by
  let β := rightMassProfile α
  have hβ : β ∈ scalarProfiles := rightMassProfile_mem hα
  have hc (x : ℝ) : ContinuousWithinAt β.val (Ici x) x :=
    continuousWithinAt_rightLim_Ici (α.property.2.tendsto_rightLim x)
  have hmb : ∀ γ ∈ scalarProfiles, scalarParisiValue hT β ≤ scalarParisiValue hT γ := by
    intro γ hγ
    rw [scalarParisiValue_congr_ae hT (rightMassProfile_ae α)]
    exact hmin γ hγ
  have hh := scalarMinimizer_one_not_support_rc hT β hβ hc hmb
  rwa [profileStieltjes_rightMass α] at hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarMinimizer_support_eq_initial_interval {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    ∃ q ∈ Ioo (0:ℝ) 1, (profileStieltjes α).measure.support=Icc 0 q := by
  have hsub : (profileStieltjes α).measure.support ⊆ Icc (0:ℝ) 1 :=
    Measure.support_subset_of_isClosed isClosed_Icc (profileStieltjes_carried hα)
  have hco : IsCompact (profileStieltjes α).measure.support :=
    isCompact_Icc.of_isClosed_subset Measure.isClosed_support hsub
  obtain ⟨u,hu,hsu⟩ := Measure.nonempty_inter_support_of_pos
    (scalarMinimizer_origin_accumulates hT α hα hmin zero_lt_one)
  obtain ⟨q,hq,hmax⟩ := hco.exists_isGreatest ⟨u,hsu⟩
  have hq0 : 0 < q := hu.1.trans_le (hmax hsu)
  have hq1 : q < 1 := lt_of_le_of_ne (hsub hq).2 (by
    intro he
    subst q
    exact scalarMinimizer_one_not_support (zero_lt_one.trans hT) α hα hmin hq)
  refine ⟨q,⟨hq0,hq1⟩,Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨(hsub hx).1,hmax hx⟩
  · exact scalarMinimizer_support_initial_interval hT α hα hmin ⟨hq0,hq1⟩ hq

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarMinimizer_support_self_consistency {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) {s : ℝ}
    (hs : s ∈ (profileStieltjes α).measure.support) :
    scalarPlantedEnergy (zero_lt_one.trans hT) α s=s := by
  have hsub : (profileStieltjes α).measure.support ⊆ Icc (0:ℝ) 1 :=
    Measure.support_subset_of_isClosed isClosed_Icc (profileStieltjes_carried hα)
  have hi (x : ℝ) (hx : x ∈ (profileStieltjes α).measure.support ∩ Ioi 0) :
      scalarPlantedEnergy (zero_lt_one.trans hT) α x=x := by
    exact scalarMinimizer_support_stationarity hT α hα hmin ⟨hx.2,
      lt_of_le_of_ne (hsub hx.1).2 (by
        intro he
        subst x
        exact scalarMinimizer_one_not_support (zero_lt_one.trans hT) α hα hmin hx.1)⟩ hx.1
  obtain h0 | h0 := (hsub hs).1.eq_or_lt
  · subst s
    have hz := scalarMinimizer_zero_mem_closure_support hT α hα hmin
    exact closure_minimal (fun x hx => hi x hx)
      (isClosed_eq (scalarPlantedEnergy_continuous (zero_lt_one.trans hT) α) continuous_id) hz
  · exact hi s ⟨hs,h0⟩

theorem scalarParisiValue_attains_interval_support {T : ℝ} (hT : 1 < T) :
    ∃ (α : boundedMassProfiles) (q : ℝ), α ∈ scalarProfiles ∧ q ∈ Ioo (0:ℝ) 1 ∧
      (∀ s, ContinuousWithinAt α.val (Ici s) s) ∧
      IsProbabilityMeasure (profileStieltjes α).measure ∧
      (∀ s, cdf (profileStieltjes α).measure s=α.val s) ∧
      (∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
        scalarParisiValue (zero_lt_one.trans hT) β) ∧
      (profileStieltjes α).measure.support=Icc 0 q ∧
      (profileStieltjes α).measure {(0:ℝ)}=0 ∧ α.val 0=0 ∧
      (∀ s ∈ Icc 0 q, scalarPlantedEnergy (zero_lt_one.trans hT) α s=s) ∧
      T*((scalarTailJet (zero_lt_one.trans hT) α 0).A₁ 0 0)^2=1 := by
  obtain ⟨α,hα,hc,hp,hcdf,hmin,hzero,hno,hmar,_hacc⟩ :=
    scalarParisiValue_attains_origin_regular hT
  obtain ⟨q,hq,hs⟩ := scalarMinimizer_support_eq_initial_interval hT α hα hmin
  refine ⟨α,q,hα,hq,hc,hp,hcdf,hmin,hs,hno,hzero,?_,hmar⟩
  intro s hsq
  exact scalarMinimizer_support_self_consistency hT α hα hmin (by rwa [hs])

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarMinimizer_cdf_zero {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) : profileStieltjes α 0=0 := by
  have hz := scalarMinimizer_measure_origin_zero hT α hα hmin
  rw [(profileStieltjes α).measure_singleton,profileStieltjes_left_zero hα,sub_zero] at hz
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) ((rightMassProfile α).property.1 0).1

theorem scalarProfile_cdf_strictMono {α : boundedMassProfiles} {q : ℝ}
    (hs : (profileStieltjes α).measure.support=Icc 0 q) :
    StrictMonoOn (profileStieltjes α) (Icc 0 q) := by
  intro x hx y hy hxy
  have hm : (x+y)/2 ∈ (profileStieltjes α).measure.support := by
    rw [hs]
    constructor <;> linarith [hx.1,hy.2]
  have hm' : (x+y)/2 ∈ (profileStieltjes (rightMassProfile α)).measure.support := by
    rwa [profileStieltjes_rightMass α]
  exact profileStieltjes_support_strict (rightMassProfile α) hm' (by linarith) (by linarith)

theorem scalarProfile_cdf_top {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) {q : ℝ}
    (hs : (profileStieltjes α).measure.support=Icc 0 q) : profileStieltjes α q=1 := by
  have hz : (profileStieltjes α).measure (Ioi q)=0 := by
    apply measure_mono_null _ Measure.measure_compl_support
    intro x hx
    rw [hs]
    exact fun hh => (not_le_of_gt hx) hh.2
  rw [(profileStieltjes α).measure_Ioi
    (scalarProfile_tendsto_top (rightMassProfile_mem hα))] at hz
  exact le_antisymm ((rightMassProfile α).property.1 q).2
    (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarSupport_curvature_marginality {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q < 1)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hs : (profileStieltjes α).measure.support=Icc 0 q)
    (hΓ : ∀ s ∈ Icc 0 q, scalarPlantedEnergy hT α s=s) :
    ∀ s ∈ Icc 0 q, T*scalarPlantedCurvature hT α s=1 := by
  have hD (s : ℝ) (hxs : s ∈ Ioo (0:ℝ) q) : T*scalarPlantedCurvature hT α s=1 := by
    have hp : 0 < s/2 := by linarith [hxs.1]
    have hps : s/2 < s := by linarith [hxs.1]
    have hpos : 0 < α.val (s/2) := by
      have hh := scalarProfile_cdf_strictMono hs ⟨le_rfl,hq.le⟩
        ⟨hp.le,by linarith [hxs.2]⟩ hp
      change α.val.rightLim 0 < α.val.rightLim (s/2) at hh
      rw [(hc 0).rightLim_eq,(hc (s/2)).rightLim_eq] at hh
      exact ((α.property.1 0).1).trans_lt hh
    have hd := scalarPlantedEnergy_derivative hT α hp.le hps (hxs.2.trans hq1) hpos
      (fun x _ => hc x)
    have he : HasDerivAt (scalarPlantedEnergy hT α) 1 s := by
      apply (hasDerivAt_id s).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hxs.1 hxs.2] with u hu
      exact hΓ u ⟨hu.1.le,hu.2.le⟩
    exact hd.unique he
  have hclosed : IsClosed {s | T*scalarPlantedCurvature hT α s=1} :=
    isClosed_eq (continuous_const.mul (scalarPlantedCurvature_continuous hT α)) continuous_const
  have hi := closure_minimal hD hclosed
  rw [closure_Ioo hq.ne] at hi
  exact hi

theorem scalarParisiValue_attains_support_curvature {T : ℝ} (hT : 1 < T) :
    ∃ (α : boundedMassProfiles) (q : ℝ), α ∈ scalarProfiles ∧ q ∈ Ioo (0:ℝ) 1 ∧
      (∀ s, ContinuousWithinAt α.val (Ici s) s) ∧
      (∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
        scalarParisiValue (zero_lt_one.trans hT) β) ∧
      (profileStieltjes α).measure.support=Icc 0 q ∧
      α.val 0=0 ∧ (∀ s ∈ Icc 0 q, scalarPlantedEnergy (zero_lt_one.trans hT) α s=s) ∧
      (∀ s ∈ Icc 0 q, T*scalarPlantedCurvature (zero_lt_one.trans hT) α s=1) := by
  obtain ⟨α,q,hα,hq,hc,_hp,_hcdf,hmin,hs,_hno,hzero,hΓ,_hmar⟩ :=
    scalarParisiValue_attains_interval_support hT
  exact ⟨α,q,hα,hq,hc,hmin,hs,hzero,hΓ,
    scalarSupport_curvature_marginality (zero_lt_one.trans hT) α hq.1 hq.2 hc hs hΓ⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedCube_pos {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    0 < scalarPlantedJetPower hT α 1 3 q := by
  apply scalarPrefixTest_pos hT α hq hq1 hm hc
  intro y
  exact pow_pos (scalarProfileJet_curvature_pos (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) (y 0)) 3

theorem scalarSupport_cdf_positive {q s : ℝ} (α : boundedMassProfiles)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 q) (hxs : s ∈ Ioc (0:ℝ) q) :
    0 < α.val s := by
  have hh := scalarProfile_cdf_strictMono hs ⟨le_rfl,hxs.1.le.trans hxs.2⟩
    ⟨hxs.1.le,hxs.2⟩ hxs.1
  change α.val.rightLim 0 < α.val.rightLim s at hh
  rw [(hc 0).rightLim_eq,(hc s).rightLim_eq] at hh
  exact ((α.property.1 0).1).trans_lt hh

theorem scalarSupport_flux_zero {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq1 : q < 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 q)
    (hmar : ∀ x ∈ Icc 0 q, T*scalarPlantedCurvature hT α x=1)
    {s : ℝ} (hxs : s ∈ Ioo (0:ℝ) q) : scalarCurvatureFlux hT α s=0 := by
  have hp : 0 < s/2 := by linarith [hxs.1]
  have hps : s/2 < s := by linarith [hxs.1]
  have hm := scalarSupport_cdf_positive α hc hs (s:=s/2) ⟨hp,by linarith [hxs.2]⟩
  have hd := scalarPlantedCurvature_right_derivative hT α hp.le hps
    (hxs.2.trans hq1) hm (fun x _ => hc x)
  have he (u : ℝ) (hu : u ∈ Icc 0 q) : scalarPlantedCurvature hT α u=1/T := by
    apply (eq_div_iff hT.ne').mpr
    simpa only [mul_comm] using hmar u hu
  have hz : HasDerivWithinAt (scalarPlantedCurvature hT α) 0 (Ici s) s := by
    apply (hasDerivWithinAt_const s (Ici s) (1/T)).congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioo_mem_nhds hxs.1 hxs.2)] with u hu
      exact he u ⟨hu.1.le,hu.2.le⟩
    · exact he s ⟨hxs.1.le,hxs.2.le⟩
  have hz' : T*scalarCurvatureFlux hT α s=0 := by
    have heq := hd.derivWithin (uniqueDiffWithinAt_Ici s)
    rw [hz.derivWithin (uniqueDiffWithinAt_Ici s)] at heq
    exact heq.symm
  exact (mul_eq_zero.mp hz').resolve_left hT.ne'

theorem scalarSupport_cdf_ratio {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq1 : q < 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 q)
    (hmar : ∀ x ∈ Icc 0 q, T*scalarPlantedCurvature hT α x=1)
    {s : ℝ} (hxs : s ∈ Ioo (0:ℝ) q) :
    α.val s=scalarPlantedJetPower hT α 2 2 s/(2*scalarPlantedJetPower hT α 1 3 s) := by
  have hp := scalarPlantedCube_pos hT α hxs.1 (hxs.2.trans hq1).le
    (scalarSupport_cdf_positive α hc hs ⟨hxs.1,hxs.2.le⟩) (fun x _ => hc x)
  have hz := scalarSupport_flux_zero hT α hq1 hc hs hmar hxs
  apply (eq_div_iff (mul_pos (by norm_num) hp).ne').mpr
  unfold scalarCurvatureFlux at hz
  nlinarith

theorem scalarSupport_cdf_continuousAt {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq1 : q < 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 q)
    (hmar : ∀ x ∈ Icc 0 q, T*scalarPlantedCurvature hT α x=1)
    {s : ℝ} (hxs : s ∈ Ioo (0:ℝ) q) : ContinuousAt α.val s := by
  have hp := scalarPlantedCube_pos hT α hxs.1 (hxs.2.trans hq1).le
    (scalarSupport_cdf_positive α hc hs ⟨hxs.1,hxs.2.le⟩) (fun x _ => hc x)
  have hd := (scalarPlantedJetPower_continuous hT α 2 2).continuousAt.div
    ((scalarPlantedJetPower_continuous hT α 1 3).continuousAt.const_mul 2)
    (mul_pos (by norm_num) hp).ne'
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxs.1 hxs.2] with u hu
  exact scalarSupport_cdf_ratio hT α hq1 hc hs hmar hu

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def scalarThirdSlope {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q x : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, scalarTailSpatialJet hT α 4 q (fun _ => u*x)

theorem scalarThirdSlope_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × ℝ => scalarThirdSlope hT α p.1 p.2) := by
  have hp : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (p.1.1, fun _ : Fin 1 => p.2*p.1.2)) :=
    continuous_fst.fst.prodMk (continuous_pi fun _ => continuous_snd.mul continuous_fst.snd)
  have hc := (scalarTailSpatialJet_continuous hT α 4).comp hp
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun p : ℝ × ℝ => fun u : ℝ => scalarTailSpatialJet hT α 4 p.1 (fun _ => u*p.2)) hc 0 1

theorem scalarThirdSlope_zero {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) :
    scalarThirdSlope hT α q 0=scalarTailSpatialJet hT α 4 q 0 := by
  simp only [scalarThirdSlope,mul_zero,intervalIntegral.integral_const,sub_zero,one_smul]
  rfl

theorem scalarThirdSlope_bound {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q x : ℝ) :
    |scalarThirdSlope hT α q x| ≤ (ReplicaTree.attachmentCount 1 3:ℝ) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=(ReplicaTree.attachmentCount 1 3:ℝ))
    (f:=fun u => scalarTailSpatialJet hT α 4 q (fun _ => u*x))
    (fun u _ => by
      rw [Real.norm_eq_abs]
      exact scalarProfileJet_bound (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) _ _ 3 (u*x))
  change |∫ u in (0:ℝ)..1, scalarTailSpatialJet hT α 4 q (fun _ => u*x)| ≤ _
  simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh

theorem scalarThirdSlope_factor {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q x : ℝ) :
    scalarTailSpatialJet hT α 3 q (fun _ => x)=x*scalarThirdSlope hT α q x := by
  have hd (u : ℝ) : HasDerivAt
      (fun v : ℝ => scalarTailSpatialJet hT α 3 q (fun _ => v*x))
      (scalarTailSpatialJet hT α 4 q (fun _ => u*x)*x) u := by
    convert! (scalarProfileJet_hasDerivAt (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) 3 (u*x)).comp u
      ((hasDerivAt_id u).mul_const x) using 1
    simp only [one_mul]
    rfl
  have hc : Continuous (fun u : ℝ => scalarTailSpatialJet hT α 4 q (fun _ => u*x)*x) :=
    ((scalarTailSpatialJet_continuous hT α 4).comp
      (continuous_const.prodMk (continuous_pi fun _ => continuous_id.mul_const x))).mul_const x
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hc.intervalIntegrable 0 1)
  have hz : scalarTailSpatialJet hT α 3 q (fun _ => 0)=0 := by
    have hp := scalarProfileJet_parity (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) 3 0
    norm_num only [neg_zero,show (-1:ℝ)^3 = -1 by norm_num,neg_one_mul] at hp
    change scalarProfileJet (rescaledMassProfile α hT) (T*q)
      (Real.toNNReal (T*(1-q))) 3 0=0
    linarith
  simp only [one_mul,zero_mul,hz,sub_zero,intervalIntegral.integral_mul_const] at hi
  exact hi.symm.trans (mul_comm _ _)

end SKFluctuations.Hierarchy

end

end OAI
