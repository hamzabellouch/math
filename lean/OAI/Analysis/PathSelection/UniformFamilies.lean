import Mathlib
import OAI.Analysis.PathSelection.RecursiveClocks
import OAI.Analysis.PathSelection.SectorInduction

namespace OAI

/-! Coefficient vanishing, uniform clock expansions and holomorphic family limits. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
namespace DegeneratingTrees

 

theorem sector_common_zero_of_ray_zero {ι : Type*} {ω : ℝ → ℝ} {R : ℝ}
    (hω : AdmissibleAngularLoss ω) {f : ι → ℂ → ℂ}
    (hf : ∀ i,AnalyticOnNhd ℂ (f i) (lossSector ω R))
    (hz : ∀ i,∀ᶠ t : ℝ in atTop,f i (t:ℂ)=0) :
    ∃ W : ℝ,R≤W ∧ ∀ z∈lossSector ω W,∀ i,f i z=0 := by
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hcontrol⟩ := angularLoss_kernel_data hω
  let W := max (max R S) 1
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hWR : R≤W := (le_max_left _ _).trans (le_max_left _ _)
  have hWS : S≤W := (le_max_right _ _).trans (le_max_left _ _)
  have hsub : lossSector ω W ⊆ lossSector ω R := fun z hz => ⟨hWR.trans_lt hz.1,hz.2⟩
  have hconn : IsPreconnected (lossSector ω W) := by
    apply lossSector_isPreconnected hW0
    intro r hr
    have hh := hcontrol r (hWS.trans hr.le)
    exact ⟨hh.1,by linarith [hh.2.1,Real.pi_gt_three]⟩
  refine ⟨W,hWR,?_⟩
  intro z hzw i
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hz i)
  let x := max W T+1
  have hxW : W<x := by dsimp [x]; linarith [le_max_left W T]
  have hxT : T<x := by dsimp [x]; linarith [le_max_right W T]
  have hxpos : 0<x := hW0.trans hxW
  have hxmem : (x:ℂ)∈lossSector ω W := by
    have hh := hcontrol x (hWS.trans hxW.le)
    simp only [lossSector,mem_ofPred_eq,Complex.norm_of_nonneg hxpos.le,
      Complex.arg_ofReal_of_nonneg hxpos.le,abs_zero]
    exact ⟨hxW,by linarith [hh.2.1,Real.pi_gt_three]⟩
  have hcl : (x:ℂ)∈closure ({z | f i z=0}\{(x:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((x+ε/2:ℝ):ℂ),⟨hT _ (by linarith),?_⟩,?_⟩
    · simp only [mem_singleton_iff,Complex.ofReal_inj]
      linarith
    · simp only [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by linarith,by linarith⟩
  exact ((hf i).mono hsub).eqOn_zero_of_preconnected_of_mem_closure hconn hxmem hcl hzw

namespace Clock

 

lemma SectorExpansion.positive_coeff_zero_of_limit {K : Set (ℂ → ℂ)}
    (hK : LowerSectorData K) {F : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F E b) (hb : ∀ β∈E,b β∈K) {c : ℂ}
    (hlim : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 c))
    {β : ℝ} (hβ : β∈E) (hβpos : 0<β) :
    ∀ᶠ t : ℝ in atTop,b β (t:ℂ)=0 := by
  by_contra hn
  have ht := hF.trim_zero (fun a ha => hK.analytic (hb a ha))
  have hβn : β∈nonzeroRaySupport E b := ⟨hβ,hn⟩
  obtain ⟨a,ha,hmax⟩ := exists_greatest_of_finite_above ht.finite_above ⟨β,hβn⟩
  have hapos : 0<a := hβpos.trans_le (hmax β hβn)
  have hbne : ∀ᶠ z in sectorInfinity,b a z≠0 := by
    rcases hK.zero_or_ne (hb a ha.1) with hz | hz
    · exact False.elim (ha.2 (tendsto_real_sectorInfinity.eventually hz))
    · exact hz
  have hs := hK.slow (hK.inv_mem (hb a ha.1))
  have h1 := (ht.uniform_leading_tendsto ha hmax hbne hs).comp tendsto_real_sectorInfinity
  have he : ExpSmall 0 (fun z => Complex.exp (((-a:ℝ):ℂ)*z)) :=
    ⟨-a,by linarith,ExpBound.cexp (-a)⟩
  have h0 := ((he.mul_slow hs).tendsto_zero.comp tendsto_real_sectorInfinity).mul hlim
  have heq := tendsto_nhds_unique h0 h1
  exact zero_ne_one (by simpa only [zero_mul] using heq)

end Clock
end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
open scoped BigOperators
namespace DegeneratingTrees.Clock
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

structure UniformSectorExpansion (F : ℂ → V) (A : Set ℝ) (b : ℝ → ℂ → V) : Prop where
  bounded_above : BddAbove A
  finite_above : ∀ B : ℝ,(A ∩ Ici B).Finite
  remainders : ∀ B : ℝ,∃ (ω : ℝ → ℝ) (R ε C : ℝ),
    AdmissibleAngularLoss ω ∧ 0<ε ∧ 0≤C ∧
    AnalyticOnNhd ℂ F (lossSector ω R) ∧
    ∀ z∈lossSector ω R,
      ‖F z-∑ β∈(finite_above B).toFinset,Complex.exp ((β:ℂ)*z) • b β z‖ ≤
        C*Real.exp ((B-ε)*z.re)

lemma UniformSectorExpansion.eventually_analytic [CompleteSpace V] {F : ℂ → V} {A : Set ℝ} {b : ℝ → ℂ → V}
    (hF : UniformSectorExpansion F A b) :
    ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z := by
  obtain ⟨ω,R,ε,C,hω,hε,hC,ha,hb⟩ := hF.remainders 0
  exact ⟨ω,R,hω,ha⟩

lemma UniformSectorExpansion.scalarize [CompleteSpace V] {F : ℂ → V} {A : Set ℝ} {b : ℝ → ℂ → V}
    (hF : UniformSectorExpansion F A b) (L : V →L[ℂ] ℂ) :
    SectorExpansion (fun z => L (F z)) A (fun β z => L (b β z)) := by
  classical
  refine ⟨hF.bounded_above,hF.finite_above,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,ha,hb⟩ := hF.remainders B
  refine ⟨ω,R,ε,‖L‖*C,hω,hε,mul_nonneg (norm_nonneg _) hC,
    fun z hz => (L.analyticAt _).comp (ha z hz),?_⟩
  intro z hz
  have hh := (L.le_opNorm (F z-∑ β∈(hF.finite_above B).toFinset,
    Complex.exp ((β:ℂ)*z) • b β z)).trans
    (mul_le_mul_of_nonneg_left (hb z hz) (norm_nonneg L))
  simpa only [map_sub,map_sum,map_smul,smul_eq_mul,mul_assoc] using hh

 

lemma uniform_sector_eq_of_ray [CompleteSpace V] {F G : ℂ → V}
    (ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (hb : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ G z)
    (he : (fun t : ℝ => F (t:ℂ)) =ᶠ[atTop] fun t => G (t:ℂ)) :
    F =ᶠ[sectorInfinity] G := by
  obtain ⟨ω,R,hω,haa⟩ := ha.and hb
  obtain ⟨W,hW,hz⟩ := sector_common_zero_of_ray_zero hω
    (f := fun (L : V →L[ℂ] ℂ) z => L (F z-G z))
    (fun L z hz => (L.analyticAt _).comp ((haa z hz).1.sub (haa z hz).2))
    (fun L => he.mono (fun t ht => by
      change F (t:ℂ)=G (t:ℂ) at ht
      rw [ht,sub_self,map_zero]))
  refine ⟨ω,W,hω,fun z hz' => sub_eq_zero.mp ?_⟩
  exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (hz z hz')

 

lemma UniformSectorExpansion.positive_coeff_zero [CompleteSpace V] {K : Set (ℂ → ℂ)}
    (hK : LowerSectorData K) {F : ℂ → V} {A : Set ℝ} {b : ℝ → ℂ → V}
    (hF : UniformSectorExpansion F A b)
    (hba : ∀ β∈A,∀ᶠ z in sectorInfinity,AnalyticAt ℂ (b β) z)
    (hb : ∀ (L : V →L[ℂ] ℂ) β,β∈A → (fun z => L (b β z))∈K)
    {c : V} (hlim : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 c))
    {β : ℝ} (hβ : β∈A) (hβpos : 0<β) :
    ∀ᶠ z in sectorInfinity,b β z=0 := by
  obtain ⟨ω,R,hω,ha⟩ := hba β hβ
  obtain ⟨W,hW,hz⟩ := sector_common_zero_of_ray_zero hω
    (f := fun (L : V →L[ℂ] ℂ) z => L (b β z))
    (fun L z hz => (L.analyticAt _).comp (ha z hz))
    (fun L => (hF.scalarize L).positive_coeff_zero_of_limit hK (hb L)
      (L.continuous.continuousAt.tendsto.comp hlim) hβ hβpos)
  exact ⟨ω,W,hω,fun z hz' => SeparatingDual.eq_zero_of_forall_dual_eq_zero (hz z hz')⟩

noncomputable def zeroCoefficient (A : Set ℝ) (b : ℝ → ℂ → V) (z : ℂ) : V := by
  classical
  exact if 0∈A then b 0 z else 0

 

lemma UniformSectorExpansion.zero_cutoff_error [CompleteSpace V] {F : ℂ → V} {A : Set ℝ} {b : ℝ → ℂ → V}
    (hF : UniformSectorExpansion F A b)
    (hz : ∀ β∈A,0<β → ∀ᶠ z in sectorInfinity,b β z=0) :
    Tendsto (fun z => F z-zeroCoefficient A b z) sectorInfinity (𝓝 0) := by
  classical
  unfold zeroCoefficient
  obtain ⟨ω,R,ε,C,hω,hε,hC,hFa,hbound⟩ := hF.remainders 0
  have hh : ∀ᶠ z in sectorInfinity,∀ β∈(hF.finite_above 0).toFinset,β≠0 → b β z=0 := by
    rw [Filter.eventually_all_finset]
    intro β hβ
    by_cases he : β=0
    · exact Eventually.of_forall (fun z hn => (hn he).elim)
    · have hb := (hF.finite_above 0).mem_toFinset.mp hβ
      exact (hz β hb.1 (lt_of_le_of_ne hb.2 (Ne.symm he))).mono (fun z hz _ => hz)
  have hbd : ∀ᶠ z in sectorInfinity,
      ‖F z-(if 0∈A then b 0 z else 0)‖≤C*Real.exp (-ε*z.re) := by
    filter_upwards [hh,(show ∀ᶠ z in sectorInfinity,z∈lossSector ω R from ⟨ω,R,hω,fun _ h=>h⟩)] with z hz hzr
    have hsum : (∑ β∈(hF.finite_above 0).toFinset,Complex.exp ((β:ℂ)*z) • b β z) =
        if 0∈A then b 0 z else 0 := by
      by_cases h0 : (0:ℝ)∈A
      · rw [ite_eq_left h0,Finset.sum_eq_single 0]
        · simp
        · intro β hβ hβ0; rw [hz β hβ hβ0,smul_zero]
        · intro hn
          exact False.elim (hn ((hF.finite_above 0).mem_toFinset.mpr ⟨h0,by simp⟩))
      · rw [ite_eq_right h0]
        apply Finset.sum_eq_zero
        intro β hβ
        have hn : β≠0 := by
          intro he; subst β
          exact h0 ((hF.finite_above 0).mem_toFinset.mp hβ).1
        rw [hz β hβ hn,smul_zero]
    simpa only [hsum,zero_sub] using hbound z hzr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun z : ℂ => C*Real.exp (-ε*z.re)) sectorInfinity (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using (Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (show -ε<0 by linarith)).mpr
        tendsto_re_sectorInfinity)).const_mul C
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbd ht

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def UniformPuiseux (f : ℝ → V) : Prop :=
  ∃ n : ℕ,0<n ∧ ∃ m : ℤ,∃ F : ℂ → V,AnalyticAt ℂ F 0 ∧
    f =ᶠ[atTop] fun t => (rootCoord n t:ℂ)^m • F (rootCoord n t)

lemma UniformPuiseux.scalarize [CompleteSpace V] {f : ℝ → V} (hf : UniformPuiseux f)
    (L : V →L[ℂ] ℂ) : Puiseux (fun t => L (f t)) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  refine ⟨n,hn,m,fun z => L (F z),(L.analyticAt _).comp hF,?_⟩
  filter_upwards [he] with t ht
  rw [ht,map_smul]
  simp only [←Complex.ofReal_zpow,Complex.real_smul,smul_eq_mul]

lemma UniformPuiseux.normalize [CompleteSpace V] {f : ℝ → V} (hf : UniformPuiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    ∃ n : ℕ,0<n ∧ ∃ m : ℤ,∃ F : ℂ → V,
      AnalyticAt ℂ F 0 ∧ F 0≠0 ∧
      f =ᶠ[atTop] fun t => (rootCoord n t:ℂ)^m • F (rootCoord n t) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  have hFne : ¬ F =ᶠ[𝓝 0] fun _ => 0 := by
    intro h0; apply hne
    filter_upwards [he,(rootCoord_complex_tendsto_zero hn).eventually h0] with t ht hz
    simp [ht,hz]
  obtain ⟨k,G,hG,hG0,hfac⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hFne
  refine ⟨n,hn,m+(k:ℤ),G,hG,hG0,?_⟩
  filter_upwards [he,(rootCoord_complex_tendsto_zero hn).eventually hfac,
    eventually_gt_atTop (0:ℝ)] with t ht hfac htpos
  have hr : (rootCoord n t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (rootCoord_pos htpos).ne'
  rw [ht,hfac,sub_zero,zpow_add₀ hr,zpow_natCast,smul_smul]

lemma UniformPuiseux.finite_limit_nonnegative [CompleteSpace V] {f : ℝ → V} {d : V}
    (hlim : Tendsto f atTop (𝓝 d)) {n : ℕ} (hn : 0<n) {m : ℤ} {F : ℂ → V}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0≠0)
    (he : f =ᶠ[atTop] fun t => (rootCoord n t:ℂ)^m • F (rootCoord n t)) :
    0 ≤ m := by
  by_contra hmn
  have hm : m<0 := lt_of_not_ge hmn
  let k : ℕ := (-m).toNat
  have hk : 0<k := by omega
  have hkm : (k:ℤ)=-m := Int.toNat_of_nonneg (neg_nonneg.mpr hm.le)
  have h0 : Tendsto (fun t => (rootCoord n t:ℂ)^k • f t) atTop (𝓝 0) := by
    simpa only [zero_pow hk.ne',zero_smul] using ((rootCoord_complex_tendsto_zero hn).pow k).smul hlim
  have he' : (fun t => (rootCoord n t:ℂ)^k • f t) =ᶠ[atTop]
      fun t => F (rootCoord n t) := by
    filter_upwards [he,eventually_gt_atTop (0:ℝ)] with t ht htpos
    have hr : (rootCoord n t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (rootCoord_pos htpos).ne'
    rw [ht,smul_smul,←zpow_natCast,←zpow_add₀ hr,hkm,neg_add_cancel,zpow_zero,one_smul]
  exact hF0 (tendsto_nhds_unique (hF.continuousAt.tendsto.comp
    (rootCoord_complex_tendsto_zero hn)) (h0.congr' he'))

 

lemma UniformPuiseux.finite_limit_representative [CompleteSpace V] {f : ℝ → V} (hf : UniformPuiseux f)
    {d : V} (hlim : Tendsto f atTop (𝓝 d)) :
    ∃ (G : ℂ → V) (R : ℝ),
      (∀ z : ℂ,R<‖z‖ → 0<z.re → AnalyticAt ℂ G z) ∧
      (f =ᶠ[atTop] fun t => G (t:ℂ)) ∧ Tendsto G radialInfinity (𝓝 d) := by
  by_cases hz : f =ᶠ[atTop] fun _ => 0
  · have hd : d=0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hz.symm)
    subst d
    exact ⟨fun _ => 0,0,fun _ _ _ => analyticAt_const,hz,tendsto_const_nhds⟩
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.normalize hz
  have hm := UniformPuiseux.finite_limit_nonnegative hlim hn hF hF0 he
  let k := m.toNat
  have hkm : (k:ℤ)=m := Int.toNat_of_nonneg hm
  let G : ℂ → V := fun z => (complexRoot n z)^k • F (complexRoot n z)
  have heG : f =ᶠ[atTop] fun t => G (t:ℂ) := by
    filter_upwards [he,eventually_gt_atTop (0:ℝ)] with t ht htpos
    simpa only [G,complexRoot_real htpos.le,←zpow_natCast,hkm] using ht
  have hconst : d=(0:ℂ)^k • F 0 := by
    have ht := ((rootCoord_complex_tendsto_zero hn).pow k).smul
      (hF.continuousAt.tendsto.comp (rootCoord_complex_tendsto_zero hn))
    apply tendsto_nhds_unique hlim
    apply ht.congr'
    filter_upwards [he] with t ht
    simpa only [Function.comp_apply,←zpow_natCast,hkm] using ht.symm
  obtain ⟨R,hR⟩ := radial_eventually ((complexRoot_tendsto_zero hn).eventually hF.eventually_analyticAt)
  refine ⟨G,R,?_,heG,?_⟩
  · intro z hz hzre
    have hr := complexRoot_analytic (n := n) hzre
    exact (hr.pow k).smul ((hR z hz).comp hr)
  · rw [hconst]
    exact ((complexRoot_tendsto_zero hn).pow k).smul
      (hF.continuousAt.tendsto.comp (complexRoot_tendsto_zero hn))

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

def UniformClockGerm : List (ℝ → ℝ) → (ℝ → V) → Prop
  | [], f => UniformPuiseux f
  | X::xs,f => ∃ (F : ℂ → V) (A : Set ℝ) (b : ℝ → ℂ → V),
      UniformSectorExpansion F A b ∧
      (∀ β∈A,UniformClockGerm xs (fun t => b β (X t:ℂ)) ∧
        ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (b β) z) ∧
      f =ᶠ[atTop] fun t => F (X t:ℂ)

lemma UniformClockGerm.scalarize {xs : List (ℝ → ℝ)} {f : ℝ → V}
    (hf : UniformClockGerm xs f) (L : V →L[ℂ] ℂ) : ClockGerm xs (fun t => L (f t)) := by
  induction xs generalizing f with
  | nil => exact UniformPuiseux.scalarize hf L
  | cons X xs ih =>
    obtain ⟨F,A,b,hF,hb,he⟩ := hf
    refine ⟨fun z => L (F z),A,fun β z => L (b β z),hF.scalarize L,?_,?_⟩
    · intro β hβ
      exact ⟨ih (hb β hβ).1,((hb β hβ).2).mono (fun z ha => (L.analyticAt _).comp ha)⟩
    · exact he.mono (fun _ he => congrArg L he)

 

lemma UniformPuiseux.first_clock_limit {f : ℝ → V} (hf : UniformPuiseux f)
    {X : ℝ → ℝ} {a : ℝ} (ha : 0<a) (hX : X =ᶠ[atTop] fun t => a*t)
    {F : ℂ → V} (hFa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (he : f =ᶠ[atTop] fun t => F (X t:ℂ)) {d : V}
    (hlim : Tendsto f atTop (𝓝 d)) : Tendsto F sectorInfinity (𝓝 d) := by
  obtain ⟨G,R,hGa,heG,hGt⟩ := hf.finite_limit_representative hlim
  have ha0 : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  let I : ℂ → ℂ := fun z => z/(a:ℂ)
  have hIt : Tendsto I sectorInfinity radialInfinity := by
    rw [radialInfinity,tendsto_comap_iff]
    simpa only [I,Function.comp_def,norm_div,Complex.norm_of_nonneg ha.le] using
      tendsto_norm_sectorInfinity.atTop_div_const ha
  have hIa : ∀ z : ℂ,AnalyticAt ℂ I z := fun z => analyticAt_id.div_const
  have hGIa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => G (I z)) z := by
    have hn : ∀ᶠ z in sectorInfinity,R<‖I z‖ :=
      (tendsto_comap_iff.mp hIt).eventually (eventually_gt_atTop R)
    filter_upwards [hn,tendsto_re_sectorInfinity.eventually (eventually_gt_atTop (0:ℝ))]
      with z hz hre
    have hIre : 0<(I z).re := by
      simpa only [I,Complex.div_ofReal_re] using div_pos hre ha
    exact (hGa (I z) hz hIre).comp (hIa z)
  have hline : (fun t : ℝ => F (t:ℂ)) =ᶠ[atTop] fun t => G (I (t:ℂ)) := by
    have hscale : Tendsto (fun t : ℝ => t/a) atTop atTop := tendsto_id.atTop_div_const ha
    filter_upwards [hscale.eventually he,hscale.eventually heG,hscale.eventually hX] with t he heG hX
    change f (t/a)=F (X (t/a):ℂ) at he
    change f (t/a)=G (t/a:ℝ) at heG
    have hx : X (t/a)=t := by rw [hX]; field_simp
    rw [hx] at he
    simpa only [I,←Complex.ofReal_div] using he.symm.trans heG
  exact (hGt.comp hIt).congr' (uniform_sector_eq_of_ray hFa hGIa hline).symm

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma tendsto_of_comp_clock {W : Type*} {l : Filter W} {F : ℝ → W}
    {X : ℝ → ℝ} (hXt : Tendsto X atTop atTop)
    (hXc : ∀ᶠ t in atTop,ContinuousAt X t)
    (hF : Tendsto (fun t => F (X t)) atTop l) : Tendsto F atTop l := by
  rw [Filter.tendsto_def] at hF ⊢
  intro s hs
  exact eventually_of_comp_clock hXt hXc (hF s hs)

lemma ValidClocks.previous_chart {xs : List (ℝ → ℝ)} {X Y : ℝ → ℝ}
    (hvalid : ValidClocks (X::Y::xs)) :
    ∃ y : ℂ → ℂ,(∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z) ∧
      Tendsto y sectorInfinity sectorInfinity ∧
      (∀ᶠ t : ℝ in atTop,y (X t:ℂ)=(Y t:ℂ)) := by
  obtain ⟨K,hD⟩ := hvalid.1.sectorData
  have hYt := hvalid.1.2.2.1
  have hXt := hvalid.2.2.1
  have hYc := (hvalid.1.2.1.real_eventually_analytic hvalid.1.1).mono (fun _ h => h.continuousAt)
  obtain ⟨H,hH,he⟩ := hD.expansion_iff.mp hvalid.2.1
  have hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re := by
    apply eventually_of_comp_clock hYt hYc
    filter_upwards [he,hXt.eventually (eventually_gt_atTop 0)] with t he hx
    rw [←he]
    exact ⟨rfl,hx⟩
  have hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop := by
    apply tendsto_of_comp_clock hYt hYc
    apply hXt.congr'
    exact he.mono (fun t ht => (congrArg Complex.re ht))
  have hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    apply eventually_of_comp_clock hYt hYc
    filter_upwards [he,hvalid.2.2.2.def hε] with t he ht
    change ‖Y t‖≤ε*‖(H (Y t:ℂ)).re‖
    rwa [←he]
  obtain ⟨y,I,hi,hfamily⟩ := hD.charts H hH hHr hHt hfast
  refine ⟨y,hi.analytic_left.mono (fun _ h => h.1),hi.maps_sector,?_⟩
  filter_upwards [he,hYt.eventually hi.right] with t he hy
  rwa [he]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

lemma uniform_expansion_limit {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    (hvalid : ValidClocks (X::xs)) {F : ℂ → V} {A : Set ℝ} {b : ℝ → ℂ → V}
    (hF : UniformSectorExpansion F A b)
    (hb : ∀ β∈A,UniformClockGerm xs (fun t => b β (X t:ℂ)) ∧
      ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (b β) z)
    (hlower : ∀ β∈A,∀ c : V,Tendsto (fun t => b β (X t:ℂ)) atTop (𝓝 c) →
      Tendsto (b β) sectorInfinity (𝓝 c))
    {d : V} (hlim : Tendsto (fun t => F (X t:ℂ)) atTop (𝓝 d)) :
    Tendsto F sectorInfinity (𝓝 d) := by
  classical
  obtain ⟨K,hD⟩ := hvalid.sectorData
  have hXt := hvalid.2.2.1
  have hXc := (hvalid.2.1.real_eventually_analytic hvalid.1).mono (fun _ h => h.continuousAt)
  have hreal : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 d) :=
    tendsto_of_comp_clock hXt hXc hlim
  have hmembers : ∀ (L : V →L[ℂ] ℂ) β,β∈A → (fun z => L (b β z))∈K := by
    intro L β hβ
    exact (hD.membership _).mpr ⟨(hb β hβ).1.scalarize L,
      ((hb β hβ).2).mono (fun z ha => (L.analyticAt _).comp ha)⟩
  have hz : ∀ β∈A,0<β → ∀ᶠ z in sectorInfinity,b β z=0 :=
    fun β hβ hpos => hF.positive_coeff_zero hD.lower
      (fun β hβ => (hb β hβ).2) hmembers hreal hβ hpos
  have herr := hF.zero_cutoff_error hz
  have hBs : Tendsto (fun t => zeroCoefficient A b (X t:ℂ)) atTop (𝓝 d) := by
    simpa only [sub_sub_cancel,sub_zero,Function.comp_apply] using
      hlim.sub (herr.comp (tendsto_real_sectorInfinity.comp hXt))
  have hBb : Tendsto (zeroCoefficient A b) sectorInfinity (𝓝 d) := by
    change Tendsto (fun z => if (0:ℝ)∈A then b 0 z else 0) sectorInfinity (𝓝 d)
    by_cases h0 : (0:ℝ)∈A
    · simpa only [zeroCoefficient,ite_eq_left h0] using
        hlower 0 h0 d (by simpa only [zeroCoefficient,ite_eq_left h0] using hBs)
    · have hd : d=0 := tendsto_nhds_unique
        (show Tendsto (fun _ : ℝ => (0:V)) atTop (𝓝 d) by
          simpa only [zeroCoefficient,ite_eq_right h0] using hBs) tendsto_const_nhds
      subst d
      simpa only [zeroCoefficient,ite_eq_right h0] using
        (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0:V)) sectorInfinity (𝓝 0))
  simpa only [sub_add_cancel,zero_add] using herr.add hBb

 

theorem UniformClockGerm.model_limit {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    (hvalid : ValidClocks (X::xs)) {f : ℝ → V} (hf : UniformClockGerm xs f)
    {F : ℂ → V} (hFa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (he : f =ᶠ[atTop] fun t => F (X t:ℂ)) {d : V}
    (hlim : Tendsto f atTop (𝓝 d)) : Tendsto F sectorInfinity (𝓝 d) := by
  induction xs generalizing X f F d with
  | nil =>
    obtain ⟨a,ha,hX⟩ := hvalid.2.2.2
    exact UniformPuiseux.first_clock_limit hf ha hX hFa he hlim
  | cons Y ys ih =>
    obtain ⟨G,A,b,hG,hb,heG⟩ := hf
    have hGt : Tendsto G sectorInfinity (𝓝 d) :=
      uniform_expansion_limit hvalid.1 hG hb
        (fun β hβ c hc => ih hvalid.1 (hb β hβ).1 (hb β hβ).2 EventuallyEq.rfl hc)
        (hlim.congr' heG)
    obtain ⟨y,hya,hyt,hyr⟩ := hvalid.previous_chart
    have hGya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => G (y z)) z := by
      filter_upwards [hya,hyt.eventually hG.eventually_analytic] with z hy hg
      exact hg.comp hy
    have hfg : F =ᶠ[sectorInfinity] fun z => G (y z) := by
      apply uniform_sector_eq_of_ray hFa hGya
      have hXc := (hvalid.2.1.real_eventually_analytic hvalid.1).mono (fun _ h => h.continuousAt)
      apply eventually_of_comp_clock hvalid.2.2.1 hXc
      filter_upwards [he,heG,hyr] with t he heG hy
      rw [hy,←he,←heG]
    exact (hGt.comp hyt).congr' hfg.symm

 

theorem UniformClockGerm.last_clock_limit {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    (hvalid : ValidClocks (X::xs)) {F : ℂ → V} {A : Set ℝ} {b : ℝ → ℂ → V}
    (hF : UniformSectorExpansion F A b)
    (hb : ∀ β∈A,UniformClockGerm xs (fun t => b β (X t:ℂ)) ∧
      ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (b β) z)
    {d : V} (hlim : Tendsto (fun t => F (X t:ℂ)) atTop (𝓝 d)) :
    Tendsto F sectorInfinity (𝓝 d) :=
  uniform_expansion_limit hvalid hF hb
    (fun β hβ c hc => (hb β hβ).1.model_limit hvalid (hb β hβ).2 EventuallyEq.rfl (d := c) hc) hlim

end DegeneratingTrees.Clock
end

end OAI
