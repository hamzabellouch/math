/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import Mathlib
import OAI.Probability.SLELocalization.ConformalKernels

namespace OAI


/-! Conformal localization and Slit Maps estimates. -/

section
noncomputable section
open Set Filter Metric Topology
open scoped Topology
namespace SLEExactGauge.SlitMaps

def liftMap {U : Set ℂ} (f : C(U,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then f ⟨z,hz⟩ else 0

@[simp] lemma liftMap_apply {U : Set ℂ} (f : C(U,ℂ)) (z : U) :
    liftMap f z = f z := by simp [liftMap,z.property]

lemma tendsto_liftMap {U : Set ℂ} (hU : IsOpen U)
    {ι : Type*} {l : Filter ι} {F : ι → C(U,ℂ)} {f : C(U,ℂ)}
    (hc : Tendsto F l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => liftMap (F i)) (liftMap f) l U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  let K' : Set U := Subtype.val ⁻¹' K
  have he : Subtype.val '' K' = K := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z,hKU hz⟩,hz,rfl⟩
  have hK' : IsCompact K' := Topology.IsEmbedding.subtypeVal.isCompact_iff.2 (he.symm ▸ hK)
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hc) K' hK'
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with i hi z hz
  simpa only [liftMap, dite_eq_left (hKU hz)] using hi ⟨z,hKU hz⟩ hz

def boundedHolomorphic (U : Set ℂ) : Set C(U,ℂ) :=
  {f | DifferentiableOn ℂ (liftMap f) U ∧ ∀ z : U, ‖f z‖ ≤ 1}

lemma boundedHolomorphic_equicontinuous {U : Set ℂ} (hU : IsOpen U) :
    Equicontinuous (fun (f : boundedHolomorphic U) (z : U) => f.val z) := by
  intro z
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds z.property)
  let δ : ℝ := min (r/2) (ε*r/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hδ,fun w hw f => ?_⟩
  have hz : (z:ℂ) ∈ closedBall (z:ℂ) (r/2) := mem_closedBall_self (by positivity)
  have hw' : (w:ℂ) ∈ closedBall (z:ℂ) (r/2) := by
    exact (show dist (w:ℂ) (z:ℂ) < δ from hw).le.trans (min_le_left _ _)
  have hsub : closedBall (z:ℂ) (r/2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith : r/2 ≤ r)).trans hrU
  have hd (x : ℂ) (hx : x ∈ closedBall (z:ℂ) (r/2)) :
      DifferentiableAt ℂ (liftMap f.val) x := f.property.1.differentiableAt (hU.mem_nhds (hsub hx))
  have hdB (x : ℂ) (hx : x ∈ closedBall (z:ℂ) (r/2)) :
      ‖deriv (liftMap f.val) x‖ ≤ 2/r := by
    have hs : closedBall x (r/2) ⊆ U := by
      have hh : closedBall x (r/2) ⊆ closedBall (z:ℂ) r := by
        apply closedBall_subset_closedBall'
        have hn := mem_closedBall.1 hx
        linarith
      exact hh.trans hrU
    have hdc : DiffContOnCl ℂ (liftMap f.val) (ball x (r/2)) :=
      f.property.1.diffContOnCl_ball hs
    have hb (y : ℂ) (hy : y ∈ sphere x (r/2)) : ‖liftMap f.val y‖ ≤ 1 := by
      exact (liftMap_apply f.val ⟨y,hs (sphere_subset_closedBall hy)⟩) ▸ f.property.2 ⟨y,hs (sphere_subset_closedBall hy)⟩
    have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r/2) hdc hb
    convert hh using 1
    field_simp
  have hb := (convex_closedBall (z:ℂ) (r/2)).norm_image_sub_le_of_norm_deriv_le hd hdB hz hw'
  have he : ‖(w:ℂ)-(z:ℂ)‖ < ε*r/4 := by
    rw [← dist_eq_norm]
    exact (show dist (w:ℂ) (z:ℂ) < δ from hw).trans_le (min_le_right _ _)
  have hrp : 0 < 2/r := by positivity
  have hprod : (2/r)*‖(w:ℂ)-(z:ℂ)‖ < ε/2 := by
    calc
      _ < (2/r)*(ε*r/4) := mul_lt_mul_of_pos_left he hrp
      _ = ε/2 := by field_simp; ring
  rw [liftMap_apply,liftMap_apply] at hb
  rw [dist_comm,dist_eq_norm]
  exact hb.trans_lt (hprod.trans_le (by linarith))

lemma boundedHolomorphic_closed {U : Set ℂ} (hU : IsOpen U) :
    IsClosed (boundedHolomorphic U) := by
  apply isClosed_of_closure_subset
  intro f hf
  have : NeBot (𝓝[boundedHolomorphic U] f) := mem_closure_iff_nhdsWithin_neBot.1 hf
  have hl : Tendsto (fun x : C(U,ℂ) => x) (𝓝[boundedHolomorphic U] f) (𝓝 f) := nhdsWithin_le_nhds
  have hd : ∀ᶠ x in 𝓝[boundedHolomorphic U] f, DifferentiableOn ℂ (liftMap x) U :=
    by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.1
  refine ⟨(tendsto_liftMap hU hl).differentiableOn hd hU,fun z => ?_⟩
  have ht : Tendsto (fun x : C(U,ℂ) => ‖x z‖) (𝓝[boundedHolomorphic U] f) (𝓝 ‖f z‖) :=
    ((ContinuousEvalConst.continuous_eval_const z).norm.continuousAt.tendsto).comp hl
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hx.2 z

lemma boundedHolomorphic_compact {U : Set ℂ} (hU : IsOpen U) :
    IsCompact (boundedHolomorphic U) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : T2Space (UniformOnFun U ℂ {K : Set U | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hc : IsCompact (closure (boundedHolomorphic U)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖:={K : Set U | IsCompact K}) (F:=fun f : C(U,ℂ) => (f : U → ℂ))
      (fun K hK => hK) ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      exact (boundedHolomorphic_equicontinuous hU).equicontinuousOn K
    · intro K hK z hz
      refine ⟨closedBall (0:ℂ) 1,isCompact_closedBall _ _,fun f hf => ?_⟩
      simpa using hf.2 z
  simpa [(boundedHolomorphic_closed hU).closure_eq] using hc

end SLEExactGauge.SlitMaps

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.SlitMaps

lemma lower_norm_of_sphere {f : ℂ → ℂ} {z : ℂ} {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c)
    (hd : DifferentiableOn ℂ f (closedBall z r))
    (hn : ∀ w ∈ closedBall z r, f w ≠ 0)
    (hb : ∀ w ∈ sphere z r, c ≤ ‖f w‖) : c ≤ ‖f z‖ := by
  have hi : DifferentiableOn ℂ (fun w => (f w)⁻¹) (closedBall z r) := hd.inv hn
  have hi' : DiffContOnCl ℂ (fun w => (f w)⁻¹) (ball z r) := by
    exact hi.diffContOnCl_ball Subset.rfl
  have hm : ‖(f z)⁻¹‖ ≤ c⁻¹ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hi'
    · intro w hw
      rw [frontier_ball z hr.ne'] at hw
      rw [norm_inv]
      exact inv_anti₀ hc (hb w hw)
    · rw [closure_ball z hr.ne']
      exact mem_closedBall_self hr.le
  rw [norm_inv] at hm
  exact (inv_le_inv₀ (norm_pos_iff.2 (hn z (mem_closedBall_self hr.le))) hc).1 hm

theorem locallyUniform_nonvanishing {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hn : ∀ᶠ i in l, ∀ z ∈ U, F i z ≠ 0)
    {a : ℂ} (ha : a ∈ U) (hfa : f a ≠ 0) : ∀ z ∈ U, f z ≠ 0 := by
  have hf := hlim.differentiableOn hF hU
  have haf : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  intro z hz hzero
  have hnot : ¬∀ᶠ w in 𝓝 z, f w = 0 := by
    intro he
    exact hfa (haf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz he ha)
  have hiso := ((haf z hz).eventually_eq_or_eventually_ne (analyticAt_const (v:=0))).resolve_left hnot
  have hmem : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  have hevent : ∀ᶠ w in 𝓝 z, w ∈ U ∧ (w ≠ z → f w ≠ 0) :=
    hmem.and (eventually_nhdsWithin_iff.1 hiso)
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hevent
  have hrsub : closedBall z r ⊆ U := fun w hw => (hrU hw).1
  have hfnz : ∀ w ∈ sphere z r, f w ≠ 0 := fun w hw =>
    (hrU (sphere_subset_closedBall hw)).2 (ne_of_mem_sphere hw hr.ne')
  have hsne : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hcfn : ContinuousOn (fun w => ‖f w‖) (sphere z r) :=
    (haf.continuousOn.mono (sphere_subset_closedBall.trans hrsub)).norm
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere z r).exists_isMinOn hsne hcfn
  let c : ℝ := ‖f w‖
  have hc : 0 < c := norm_pos_iff.2 (hfnz w hw)
  have huni : TendstoUniformlyOn F f l (sphere z r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _
      (sphere_subset_closedBall.trans hrsub) (isCompact_sphere z r)
  have hclose := Metric.tendstoUniformlyOn_iff.1 huni (c/2) (by positivity)
  have hlow : ∀ᶠ i in l, c/2 ≤ ‖F i z‖ := by
    filter_upwards [hF,hn,hclose] with i hdi hni hci
    apply lower_norm_of_sphere hr (by positivity) (hdi.mono hrsub)
      (fun v hv => hni v (hrsub hv))
    intro v hv
    have hfv := hmin hv
    have hdv := hci v hv
    have htri : ‖f v‖ ≤ ‖f v-F i v‖+‖F i v‖ := norm_le_norm_sub_add _ _
    change c ≤ ‖f v‖ at hfv
    rw [dist_eq_norm] at hdv
    linarith
  have hh := ge_of_tendsto ((hlim.tendsto_at hz).norm) hlow
  rw [hzero,norm_zero] at hh
  linarith

end SLEExactGauge.SlitMaps

end

end

section
noncomputable section
open Set Filter Metric Topology
open scoped Topology
namespace SLEExactGauge.SlitMaps

lemma locallyUniform_deriv_nonvanishing {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hn : ∀ᶠ i in l, ∀ z ∈ U, deriv (F i) z ≠ 0)
    {a : ℂ} (ha : a ∈ U) (hfa : deriv f a ≠ 0) :
    ∀ z ∈ U, deriv f z ≠ 0 := by
  apply locallyUniform_nonvanishing hU hc (hlim.deriv hF hU) _ hn ha hfa
  filter_upwards [hF] with i hi
  exact hi.deriv hU

lemma locallyUniform_injective {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hi : ∀ᶠ i in l, InjOn (F i) U)
    (hnd : ∀ z ∈ U, deriv f z ≠ 0) : InjOn f U := by
  intro x hx y hy heq
  by_contra hxy
  have hmem : U \ {x} ∈ 𝓝 y := (hU.inter isClosed_singleton.isOpen_compl).mem_nhds ⟨hy,by simpa [eq_comm] using hxy⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.1 hmem
  have hsub : ball y r ⊆ U := fun z hz => (hrU hz).1
  have hnox : ∀ z ∈ ball y r, z ≠ x := fun z hz => (hrU hz).2
  have hex : ∃ b ∈ ball y r, f b ≠ f x := by
    by_contra! hn
    have he : f =ᶠ[𝓝 y] fun _ => f x := by
      filter_upwards [ball_mem_nhds y hr] with z hz
      exact hn z hz
    exact hnd y hy (he.deriv_eq.trans (deriv_const y (f x)))
  obtain ⟨b,hb,hfb⟩ := hex
  have hl : TendstoLocallyUniformlyOn (fun i z => F i z - F i x)
      (fun z => f z - f x) l (ball y r) :=
    (hlim.mono hsub).sub ((hlim.tendsto_at hx).tendstoUniformlyOn_const _).tendstoLocallyUniformlyOn
  have hd : ∀ᶠ i in l, DifferentiableOn ℂ (fun z => F i z - F i x) (ball y r) := by
    filter_upwards [hF] with i hdi
    exact (hdi.mono hsub).sub_const _
  have hne : ∀ᶠ i in l, ∀ z ∈ ball y r, F i z - F i x ≠ 0 := by
    filter_upwards [hi] with i hii z hz
    exact sub_ne_zero.2 (fun hh => hnox z hz (hii (hsub hz) hx hh))
  have hh := locallyUniform_nonvanishing isOpen_ball (convex_ball y r).isPreconnected
    hl hd hne hb (sub_ne_zero.2 hfb) y (mem_ball_self hr)
  exact hh (sub_eq_zero.2 heq.symm)

def markedEmbeddings (U : Set ℂ) (a : U) (d₀ : ℝ) : Set C(U,ℂ) :=
  {f | f ∈ boundedHolomorphic U ∧ f a = 0 ∧ InjOn (liftMap f) U ∧
    (∀ z ∈ U, deriv (liftMap f) z ≠ 0) ∧ d₀ ≤ ‖deriv (liftMap f) a‖}

lemma derivative_continuousOn {U : Set ℂ} (hU : IsOpen U) (a : U) :
    ContinuousOn (fun f : C(U,ℂ) => deriv (liftMap f) a) (boundedHolomorphic U) := by
  intro f hf
  change Tendsto _ (𝓝[boundedHolomorphic U] f) _
  have hlim := tendsto_liftMap hU (show Tendsto (fun x : C(U,ℂ) => x)
    (𝓝[boundedHolomorphic U] f) (𝓝 f) from nhdsWithin_le_nhds)
  have hh : ∀ᶠ x in 𝓝[boundedHolomorphic U] f, DifferentiableOn ℂ (liftMap x) U := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.1
  exact (hlim.deriv hh hU).tendsto_at a.property

lemma markedEmbeddings_closed {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (a : U) {d₀ : ℝ} (hd₀ : 0 < d₀) : IsClosed (markedEmbeddings U a d₀) := by
  apply isClosed_of_closure_subset
  intro f hf
  have : NeBot (𝓝[markedEmbeddings U a d₀] f) := mem_closure_iff_nhdsWithin_neBot.1 hf
  have hl : Tendsto (fun x : C(U,ℂ) => x) (𝓝[markedEmbeddings U a d₀] f) (𝓝 f) := nhdsWithin_le_nhds
  have hm : ∀ᶠ x in 𝓝[markedEmbeddings U a d₀] f, x ∈ markedEmbeddings U a d₀ := self_mem_nhdsWithin
  have he : ∀ᶠ x in 𝓝[markedEmbeddings U a d₀] f, x ∈ boundedHolomorphic U := hm.mono (fun x hx => hx.1)
  have hfb : f ∈ boundedHolomorphic U := (boundedHolomorphic_closed hU).mem_of_tendsto hl he
  have hF := he.mono (fun x hx => hx.1)
  have hd := (tendsto_liftMap hU hl).deriv hF hU
  have ht := hd.tendsto_at a.property
  have hbound : d₀ ≤ ‖deriv (liftMap f) a‖ :=
    ge_of_tendsto ht.norm (hm.mono (fun x hx => hx.2.2.2.2))
  have hnz : deriv (liftMap f) a ≠ 0 := norm_pos_iff.1 (hd₀.trans_le hbound)
  have hn := locallyUniform_deriv_nonvanishing hU hc (tendsto_liftMap hU hl) hF
    (hm.mono (fun x hx => hx.2.2.2.1)) a.property hnz
  refine ⟨hfb,?_,locallyUniform_injective hU (tendsto_liftMap hU hl) hF
    (hm.mono (fun x hx => hx.2.2.1)) hn,hn,hbound⟩
  apply tendsto_nhds_unique ((ContinuousEvalConst.continuous_eval_const a).continuousAt.tendsto.comp hl)
  exact tendsto_const_nhds.congr' (hm.mono (fun x hx => hx.2.1.symm))

lemma markedEmbeddings_compact {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (a : U) {d₀ : ℝ} (hd₀ : 0 < d₀) : IsCompact (markedEmbeddings U a d₀) :=
  (boundedHolomorphic_compact hU).of_isClosed_subset (markedEmbeddings_closed hU hc a hd₀)
    (fun _ hx => hx.1)

end SLEExactGauge.SlitMaps

end

end

section
noncomputable section
open Function Filter Metric Set Complex
open scoped Pointwise Topology
namespace SLEExactGauge.SlitMaps

/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

The following conformal embedding declarations are adapted from Mathlib.Analysis.Complex.RiemannMapping.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Complex/RiemannMapping.lean

This code has been modified.
-/

theorem exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  
  
  rcases exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  
  
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  
  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  · 
    simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩
    
    use -f x
    
    
    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx
    
    rw [nhds_neg, eventually_neg]
    
    
    
    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  
  
  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩
  
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)
  
  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

end SLEExactGauge.SlitMaps

end

end

section
noncomputable section
open Set Filter Metric Topology
open scoped Topology
namespace SLEExactGauge.SlitMaps

def IsDiskEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop :=
  MapsTo f U (ball 0 1) ∧ f a = 0 ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0

lemma IsDiskEmbedding.differentiableOn {U : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : IsDiskEmbedding U a f) : DifferentiableOn ℂ f U :=
  fun z hz => (differentiableAt_of_deriv_ne_zero (hf.2.2.2 z hz)).differentiableWithinAt

lemma exists_diskEmbedding {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) : ∃ f, IsDiskEmbedding U a f := by
  obtain ⟨f,hmap,hinj,hnd⟩ := exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hU
  have hc : ‖f a‖ < 1 := mem_ball_zero_iff.1 (hmap a.property)
  refine ⟨diskAuto (f a) ∘ f,(diskAuto_mapsTo hc).comp hmap,?_,
    (diskAuto_injOn hc).comp hinj hmap,?_⟩
  · simp
  · intro z hz
    have hdz := (diskAuto_hasDerivAt hc (mem_ball_zero_iff.1 (hmap hz))).comp z
      (differentiableAt_of_deriv_ne_zero (hnd z hz)).hasDerivAt
    rw [hdz.deriv]
    exact mul_ne_zero (by
      rw [← diskAuto_deriv hc (mem_ball_zero_iff.1 (hmap hz))]
      exact diskAuto_deriv_ne hc (mem_ball_zero_iff.1 (hmap hz))) (hnd z hz)

def continuousRestriction {U : Set ℂ} (f : ℂ → ℂ) (hf : ContinuousOn f U) : C(U,ℂ) :=
  ⟨fun z => f z,(continuousOn_iff_continuous_domRestrict.1 hf)⟩

@[simp] lemma continuousRestriction_apply {U : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f U) (z : U) :
    continuousRestriction f hf z = f z := rfl

lemma lift_restriction_eqOn {U : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f U) :
    EqOn (liftMap (continuousRestriction f hf)) f U := by
  intro z hz
  exact liftMap_apply _ ⟨z,hz⟩

lemma deriv_lift_restriction {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) {z : ℂ} (hz : z ∈ U) :
    deriv (liftMap (continuousRestriction f hf)) z = deriv f z := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw
  exact lift_restriction_eqOn hf hw

lemma IsDiskEmbedding.restriction_mem {U : Set ℂ} (hU : IsOpen U) (a : U)
    {f : ℂ → ℂ} (hf : IsDiskEmbedding U a f) {d₀ : ℝ} (hd : d₀ ≤ ‖deriv f a‖) :
    continuousRestriction f hf.differentiableOn.continuousOn ∈ markedEmbeddings U a d₀ := by
  let g := continuousRestriction f hf.differentiableOn.continuousOn
  have he : EqOn (liftMap g) f U := lift_restriction_eqOn _
  refine ⟨⟨?_,fun z => (mem_ball_zero_iff.1 (hf.1 z.property)).le⟩,hf.2.1,?_,?_,?_⟩
  · exact hf.differentiableOn.congr he
  · intro z hz w hw hh
    exact hf.2.2.1 hz hw ((he hz).symm.trans (hh.trans (he hw)))
  · intro z hz
    rw [deriv_lift_restriction hU _ hz]
    exact hf.2.2.2 z hz
  · rwa [deriv_lift_restriction hU _ a.property]

lemma markedEmbeddings_isDiskEmbedding {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (a : U) {d₀ : ℝ} {f : C(U,ℂ)} (hf : f ∈ markedEmbeddings U a d₀) :
    IsDiskEmbedding U a (liftMap f) := by
  refine ⟨?_,by simpa using hf.2.1,hf.2.2.1,hf.2.2.2.1⟩
  intro z hz
  rw [mem_ball_zero_iff]
  have hle : ‖liftMap f z‖ ≤ 1 := (liftMap_apply f ⟨z,hz⟩) ▸ hf.1.2 ⟨z,hz⟩
  apply lt_of_le_of_ne hle
  intro he
  have hm : IsMaxOn (fun w => ‖liftMap f w‖) U z := by
    intro w hw
    change ‖liftMap f w‖ ≤ ‖liftMap f z‖
    rw [he]
    exact (liftMap_apply f ⟨w,hw⟩) ▸ hf.1.2 ⟨w,hw⟩
  have hh := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hc hU hf.1.1 hz hm a.property
  simp [liftMap_apply,hf.2.1,he] at hh

theorem exists_extremal_diskEmbedding {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) (a : U) :
    ∃ f, IsDiskEmbedding U a f ∧ ∀ g, IsDiskEmbedding U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  have hc : IsPreconnected U := hUc.isPathConnected.isConnected.isPreconnected
  obtain ⟨f₀,hf₀⟩ := exists_diskEmbedding hUo hUc hU a
  let d₀ := ‖deriv f₀ a‖
  have hd₀ : 0 < d₀ := norm_pos_iff.2 (hf₀.2.2.2 a a.property)
  have hnon : (markedEmbeddings U a d₀).Nonempty :=
    ⟨continuousRestriction f₀ hf₀.differentiableOn.continuousOn,hf₀.restriction_mem hUo a le_rfl⟩
  obtain ⟨f,hf,hmax⟩ := (markedEmbeddings_compact hUo hc a hd₀).exists_isMaxOn hnon
    ((derivative_continuousOn hUo a).norm.mono (fun _ hx => hx.1))
  refine ⟨liftMap f,markedEmbeddings_isDiskEmbedding hUo hc a hf,fun g hg => ?_⟩
  by_contra! hh
  have hgd : d₀ ≤ ‖deriv g a‖ := hf.2.2.2.2.trans hh.le
  have hgmem := hg.restriction_mem hUo a hgd
  have he := hmax hgmem
  change ‖deriv (liftMap (continuousRestriction g hg.differentiableOn.continuousOn)) a‖ ≤ ‖deriv (liftMap f) a‖ at he
  rw [deriv_lift_restriction hUo _ a.property] at he
  exact (not_le_of_gt hh) he

lemma diskAuto_comp_deriv {c : ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hc : ‖c‖ < 1) (hf : DifferentiableAt ℂ f z) (hz : ‖f z‖ < 1) :
    deriv (diskAuto c ∘ f) z = deriv (diskAuto c) (f z)*deriv f z :=
  ((diskAuto_hasDerivAt hc hz).differentiableAt.hasDerivAt.comp z hf.hasDerivAt).deriv

lemma square_root_boost_real {x t : ℝ} (hx : 0 < x) (hx1 : x < 1) (ht : 0 < t) :
    t < (1/(1-x^2))*(((1-(x^2)^2)*t)/(2*x)) := by
  have hden : 0 < (1-x^2)*(2*x) := mul_pos (by nlinarith) (by positivity)
  have he : (1/(1-x^2))*(((1-(x^2)^2)*t)/(2*x)) =
      ((1-(x^2)^2)*t)/((1-x^2)*(2*x)) := by
    field_simp
  rw [he,lt_div_iff₀ hden]
  have hpos : 0 < (1-x^2)*(1-x)^2*t := by
    exact mul_pos (mul_pos (by nlinarith) (sq_pos_of_ne_zero (by linarith))) ht
  nlinarith

theorem exists_diskEmbedding_improved {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (a : U) {f : ℂ → ℂ}
    (hf : IsDiskEmbedding U a f) {b : ℂ} (hb : b ∈ ball 0 1) (homit : b ∉ f '' U) :
    ∃ q, IsDiskEmbedding U a q ∧ ‖deriv f a‖ < ‖deriv q a‖ := by
  have hbn : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  let H := diskAuto b ∘ f
  have hHmap : MapsTo H U (ball 0 1) := (diskAuto_mapsTo hbn).comp hf.1
  have hHinj : InjOn H U := (diskAuto_injOn hbn).comp hf.2.2.1 hf.1
  have hHder (z : ℂ) (hz : z ∈ U) :
      deriv H z = deriv (diskAuto b) (f z)*deriv f z :=
    diskAuto_comp_deriv hbn (differentiableAt_of_deriv_ne_zero (hf.2.2.2 z hz))
      (mem_ball_zero_iff.1 (hf.1 hz))
  have hHnd (z : ℂ) (hz : z ∈ U) : deriv H z ≠ 0 := by
    rw [hHder z hz]
    exact mul_ne_zero (diskAuto_deriv_ne hbn (mem_ball_zero_iff.1 (hf.1 hz))) (hf.2.2.2 z hz)
  have hHd : DifferentiableOn ℂ H U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hHnd z hz)).differentiableWithinAt
  have hHnz (z : ℂ) (hz : z ∈ U) : H z ≠ 0 := by
    intro he
    have hh : f z = b := (diskAuto_injOn hbn) (hf.1 hz) hb (he.trans (diskAuto_self b).symm)
    exact homit ⟨z,hz,hh⟩
  have hnot : 0 ∉ H '' U := by
    rintro ⟨z,hz,he⟩
    exact hHnz z hz he
  obtain ⟨g,hgc,hgsq⟩ := Complex.exists_continuousOn_pow_eq hUc hUo hHd.continuousOn hnot two_ne_zero
  have hgnz (z : ℂ) (hz : z ∈ U) : g z ≠ 0 := by
    intro he
    exact hHnz z hz (by simpa [he] using (hgsq z).symm)
  have hgmap : MapsTo g U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    have he := congrArg norm (hgsq z)
    rw [norm_pow] at he
    have hh := mem_ball_zero_iff.1 (hHmap hz)
    nlinarith [norm_nonneg (g z)]
  have hgder (z : ℂ) (hz : z ∈ U) : HasDerivAt g (deriv H z/(2*g z)) z := by
    apply HasDerivAt.of_comp_left (hgc.continuousAt (hUo.mem_nhds hz))
      (show HasDerivAt (fun w : ℂ => w^2) (2*g z) (g z) by simpa using hasDerivAt_pow 2 (g z))
      (differentiableAt_of_deriv_ne_zero (hHnd z hz)).hasDerivAt
      (mul_ne_zero two_ne_zero (hgnz z hz))
    exact .of_forall hgsq
  have hgnd (z : ℂ) (hz : z ∈ U) : deriv g z ≠ 0 := by
    rw [(hgder z hz).deriv]
    exact div_ne_zero (hHnd z hz) (mul_ne_zero two_ne_zero (hgnz z hz))
  have hginj : InjOn g U := by
    intro z hz w hw he
    apply hHinj hz hw
    rw [← hgsq z,← hgsq w,he]
  let c := g a
  have hcn : ‖c‖ < 1 := mem_ball_zero_iff.1 (hgmap a.property)
  have hcp : 0 < ‖c‖ := norm_pos_iff.2 (hgnz a a.property)
  let q := diskAuto c ∘ g
  have hqder (z : ℂ) (hz : z ∈ U) :
      deriv q z = deriv (diskAuto c) (g z)*deriv g z :=
    diskAuto_comp_deriv hcn (hgder z hz).differentiableAt (mem_ball_zero_iff.1 (hgmap hz))
  have hq : IsDiskEmbedding U a q := by
    refine ⟨(diskAuto_mapsTo hcn).comp hgmap,?_,(diskAuto_injOn hcn).comp hginj hgmap,?_⟩
    · exact diskAuto_self c
    · intro z hz
      rw [hqder z hz]
      exact mul_ne_zero (diskAuto_deriv_ne hcn (mem_ball_zero_iff.1 (hgmap hz))) (hgnd z hz)
  refine ⟨q,hq,?_⟩
  have hcnorm : ‖c‖^2 = ‖b‖ := by
    have he := congrArg norm (hgsq a)
    simpa [H,Function.comp_def,hf.2.1,c] using he
  have hHnorm : ‖deriv H a‖ = (1-‖b‖^2)*‖deriv f a‖ := by
    rw [hHder a a.property,norm_mul,hf.2.1,diskAuto_norm_deriv_zero hbn]
  have hgnorm : ‖deriv g a‖ = ((1-‖b‖^2)*‖deriv f a‖)/(2*‖c‖) := by
    rw [(hgder a a.property).deriv,norm_div,norm_mul,hHnorm]
    norm_num [c]
  have hqnorm : ‖deriv q a‖ = (1/(1-‖c‖^2))*(((1-(‖c‖^2)^2)*‖deriv f a‖)/(2*‖c‖)) := by
    rw [hqder a a.property,norm_mul]
    change ‖deriv (diskAuto c) c‖*‖deriv g a‖ = _
    rw [diskAuto_norm_deriv_self hcn,hgnorm,← hcnorm]
  rw [hqnorm]
  exact square_root_boost_real hcp hcn (norm_pos_iff.2 (hf.2.2.2 a a.property))

end SLEExactGauge.SlitMaps

end

end

section
noncomputable section
open Set Filter Metric Function
open scoped Topology
namespace SLEExactGauge.SlitMaps

theorem exists_biholomorphic_unitDisk {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f g : ℂ → ℂ,
      MapsTo f U (ball 0 1) ∧ MapsTo g (ball 0 1) U ∧
      (∀ z ∈ U, g (f z) = z) ∧ (∀ z ∈ ball (0:ℂ) 1, f (g z) = z) ∧
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball (0:ℂ) 1) := by
  obtain ⟨a,ha⟩ := hUc.nonempty
  obtain ⟨f,hf,hmax⟩ := exists_extremal_diskEmbedding hUo hUc hU ⟨a,ha⟩
  have hsurj : SurjOn f U (ball 0 1) := by
    intro b hb
    by_contra homit
    obtain ⟨q,hq,hstrict⟩ := exists_diskEmbedding_improved hUo hUc ⟨a,ha⟩ hf hb homit
    exact (not_le_of_gt hstrict) (hmax q hq)
  let g := invFunOn f U
  have hgmap : MapsTo g (ball 0 1) U := hsurj.mapsTo_invFunOn
  have hleft : ∀ z ∈ U, g (f z) = z := hf.2.2.1.leftInvOn_invFunOn
  have hright : ∀ z ∈ ball (0:ℂ) 1, f (g z) = z := hsurj.rightInvOn_invFunOn
  refine ⟨f,g,hf.1,hgmap,hleft,hright,hf.differentiableOn,?_⟩
  intro z hz
  have hgU := hgmap hz
  have hd := (hf.differentiableOn.analyticOnNhd hUo (g z) hgU).hasStrictDerivAt
  have he : ∀ᶠ w in 𝓝 (g z), g (f w) = w := by
    filter_upwards [hUo.mem_nhds hgU] with w hw
    exact hleft w hw
  have hgd := hd.to_local_left_inverse (hf.2.2.2 (g z) hgU) he
  rw [hright z hz] at hgd
  exact hgd.hasDerivAt.differentiableAt.differentiableWithinAt

end SLEExactGauge.SlitMaps

end

end

end OAI
