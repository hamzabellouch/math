import OAI.Analysis.StrictMeans.DerivativeDistortion

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

theorem locallyUniformLimit_zero_eventually {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hzero : ∀ᶠ n in l, ∀ w ∈ U, F n w ≠ 0)
    (hfz : f z = 0) : ∀ᶠ w in 𝓝 z, f w = 0 := by
  have hfd := hlim.differentiableOn hF hU
  have hfa := hfd.analyticAt (hU.mem_nhds hz)
  by_contra hn
  have hnz := hfa.eventually_eq_zero_or_eventually_ne_zero.resolve_left hn
  have hne : ∀ᶠ w in 𝓝 z, w ∈ U ∧ (w ≠ z → f w ≠ 0) :=
    Filter.Eventually.and (hU.mem_nhds hz) (eventually_nhdsWithin_iff.mp hnz)
  obtain ⟨R, hR, hRi⟩ := Metric.eventually_nhds_iff.mp hne
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hc : closedBall z r ⊆ U := fun w hw => (hRi (closedBall_subset_ball hrR hw)).1
  have hsne : ∀ w ∈ sphere z r, f w ≠ 0 := by
    intro w hw
    exact (hRi (closedBall_subset_ball hrR (sphere_subset_closedBall hw))).2
      (ne_of_mem_sphere hw hr.ne')
  have hcont : ContinuousOn (fun w => ‖f w‖) (sphere z r) :=
    (hfd.continuousOn.mono (sphere_subset_closedBall.trans hc)).norm
  obtain ⟨a, ha, hamin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hcont
  let δ := ‖f a‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hsne a ha)
  have hb : ∀ w ∈ sphere z r, δ ≤ ‖f w‖ := fun w hw => hamin hw
  have hu : TendstoUniformlyOn F f l (sphere z r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _
      (sphere_subset_closedBall.trans hc) (isCompact_sphere z r)
  have he1 : ∀ᶠ n in l, ∀ w ∈ sphere z r, dist (f w) (F n w) < δ / 2 :=
    tendstoUniformlyOn_iff.mp hu (δ / 2) (half_pos hδ)
  have hc0 : Tendsto (fun n => ‖F n z‖) l (𝓝 0) := by
    simpa only [hfz, norm_zero] using (hlim.tendsto_at hz).norm
  have he2 : ∀ᶠ n in l, ‖F n z‖ < δ / 2 :=
    hc0.eventually (eventually_lt_nhds (half_pos hδ))
  obtain ⟨n, hfn, hnzero, hnsph, hnz⟩ := (hF.and (hzero.and (he1.and he2))).exists
  have hginv : DifferentiableOn ℂ (fun w => (F n w)⁻¹) U := hfn.inv hnzero
  have hmax : ‖(F n z)⁻¹‖ ≤ 2 / δ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hginv.diffContOnCl_ball hc)
    · intro w hw
      rw [frontier_ball _ hr.ne'] at hw
      have htri := norm_le_norm_add_norm_sub (F n w) (f w)
      rw [norm_sub_rev (F n w) (f w)] at htri
      have hclose : ‖f w - F n w‖ < δ / 2 := by simpa only [dist_eq_norm] using hnsph w hw
      have hl : δ / 2 ≤ ‖F n w‖ := by linarith [hb w hw]
      rw [norm_inv]
      calc
        ‖F n w‖⁻¹ ≤ (δ / 2)⁻¹ := inv_anti₀ (half_pos hδ) hl
        _ = 2 / δ := by field_simp
    · exact subset_closure (mem_ball_self hr)
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (norm_pos_iff.mpr (hnzero z hz)) hδ] at hmax
  linarith

theorem locallyUniformLimit_injOn_or_constant {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ᶠ n in l, InjOn (F n) U) :
    InjOn f U ∨ ∃ c : ℂ, EqOn f (fun _ => c) U := by
  classical
  by_cases hi : InjOn f U
  · exact Or.inl hi
  right
  rw [Set.InjOn] at hi
  push Not at hi
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hi
  have hconst : TendstoUniformlyOn (fun n (_ : ℂ) => F n a) (fun _ => f a) l U := by
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (hlim.tendsto_at ha) ε hε] with n hn w _
    simpa only [dist_comm] using hn
  have hsub : TendstoLocallyUniformlyOn (fun n w => F n w - F n a)
      (fun w => f w - f a) l U :=
    (uniformContinuous_fst.sub uniformContinuous_snd).comp_tendstoLocallyUniformlyOn
      (hlim.prodMk hconst.tendstoLocallyUniformlyOn)
  have hopen : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
  have hb' : b ∈ U \ {a} := ⟨hb, by simpa only [mem_singleton_iff] using hne.symm⟩
  have hd : ∀ᶠ n in l, DifferentiableOn ℂ (fun w => F n w - F n a) (U \ {a}) := by
    filter_upwards [hF] with n hn
    exact (hn.sub_const _).mono sdiff_subset
  have hnonzero : ∀ᶠ n in l, ∀ w ∈ U \ {a}, F n w - F n a ≠ 0 := by
    filter_upwards [hinj] with n hn w hw
    exact sub_ne_zero.mpr (fun he => hw.2 (hn hw.1 ha he))
  have he := locallyUniformLimit_zero_eventually hopen hb' (hsub.mono sdiff_subset)
    hd hnonzero (sub_eq_zero.mpr hab.symm)
  have hfd := hlim.differentiableOn hF hU
  have han : AnalyticOnNhd ℂ (fun w => f w - f a) U :=
    (hfd.analyticOnNhd hU).sub analyticOnNhd_const
  have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hb he
  exact ⟨f a, fun w hw => sub_eq_zero.mp (hz hw)⟩

theorem locallyUniformLimit_injOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hz : z ∈ U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ᶠ n in l, InjOn (F n) U) (hderiv : deriv f z ≠ 0) : InjOn f U := by
  obtain hi | ⟨c, hc⟩ := locallyUniformLimit_injOn_or_constant hU hconn hlim hF hinj
  · exact hi
  exfalso
  have he : f =ᶠ[𝓝 z] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hz) hc
  exact hderiv (he.deriv_eq.trans (deriv_const _ _))

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

abbrev UnitDisk := ball (0 : ℂ) 1

instance : LocallyCompactSpace UnitDisk := isOpen_ball.locallyCompactSpace

def diskExtension (f : C(UnitDisk, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ ball (0 : ℂ) 1 then f ⟨z, h⟩ else 0

@[simp] lemma diskExtension_coe (f : C(UnitDisk, ℂ)) (z : UnitDisk) :
    diskExtension f z = f z := by simp [diskExtension]

def DiskNormalized (f : C(UnitDisk, ℂ)) : Prop :=
  DifferentiableOn ℂ (diskExtension f) (ball 0 1) ∧
  InjOn (diskExtension f) (ball 0 1) ∧
  diskExtension f 0 = 0 ∧ deriv (diskExtension f) 0 = 1

abbrev DiskFamily := {f : C(UnitDisk, ℂ) // DiskNormalized f}

lemma diskExtension_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → C(UnitDisk, ℂ)} {f : C(UnitDisk, ℂ)} (h : Tendsto F l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun n => diskExtension (F n)) (diskExtension f) l
      (ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def, diskExtension_coe] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

lemma disk_derivative_bound {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) (h1 : deriv f 0 = 1) {r : ℝ} (hr : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ r) : ‖deriv f z‖ ≤ (1 + r) / (1 - r) ^ 3 := by
  have hzr := hz.trans_lt hr
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hb := (derivative_distortion hd hi h1 hzr).2
  have hp : 0 < 1 - r := sub_pos.mpr hr
  have hden : 0 < (1 - r) ^ 3 := pow_pos hp _
  refine hb.trans (div_le_div₀ (by positivity) (by linarith) hden ?_)
  exact pow_le_pow_left₀ hp.le (by linarith) 3

lemma disk_lipschitz_bound {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) (h1 : deriv f 0 = 1) {r : ℝ} (hr : r < 1)
    {z w : ℂ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖f w - f z‖ ≤ ((1 + r) / (1 - r) ^ 3) * ‖w - z‖ := by
  apply (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
      (fun a ha => hd.differentiableAt (isOpen_ball.mem_nhds (by
        simpa only [mem_ball, dist_zero_right] using
          (show ‖a‖ ≤ r from by simpa only [mem_closedBall, dist_zero_right] using ha).trans_lt hr)))
      (fun a ha => disk_derivative_bound hd hi h1 hr (by
        simpa only [mem_closedBall, dist_zero_right] using ha))
  · simpa using hz
  · simpa using hw

lemma disk_family_pointwise_bounded (z : UnitDisk) :
    ∃ R : ℝ, ∀ f : DiskFamily, ‖f.val z‖ ≤ R := by
  refine ⟨((1 + ‖(z : ℂ)‖) / (1 - ‖(z : ℂ)‖) ^ 3) * ‖(z : ℂ)‖, ?_⟩
  intro f
  have h := disk_lipschitz_bound f.property.1 f.property.2.1 f.property.2.2.2
    (show ‖(z : ℂ)‖ < 1 by simpa only [mem_ball, dist_zero_right] using z.property)
    (z := 0) (w := z) (by simp) (le_refl _)
  simpa only [f.property.2.2.1, diskExtension_coe, sub_zero] using h

lemma disk_family_equicontinuous : Equicontinuous (fun f : DiskFamily => (f.val : UnitDisk → ℂ)) := by
  intro z
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let r := (1 + ‖(z : ℂ)‖) / 2
  have hz : ‖(z : ℂ)‖ < 1 := by simpa only [mem_ball, dist_zero_right] using z.property
  have hzr : ‖(z : ℂ)‖ < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hr0 : 0 < r := (norm_nonneg _).trans_lt hzr
  let C := (1 + r) / (1 - r) ^ 3
  have hC : 0 < C := div_pos (by linarith) (pow_pos (sub_pos.mpr hr) _)
  refine ⟨min (r - ‖(z : ℂ)‖) (ε / C), lt_min (sub_pos.mpr hzr) (div_pos hε hC), ?_⟩
  intro w hw f
  have hw' : ‖(w : ℂ) - z‖ < min (r - ‖(z : ℂ)‖) (ε / C) := by simpa only [Subtype.dist_eq, dist_eq_norm] using hw
  have hwr : ‖(w : ℂ)‖ ≤ r := by
    have ht := norm_le_norm_add_norm_sub (z : ℂ) (w : ℂ)
    rw [norm_sub_rev (z : ℂ) (w : ℂ)] at ht
    linarith [hw'.trans_le (min_le_left _ _)]
  have h := disk_lipschitz_bound f.property.1 f.property.2.1 f.property.2.2.2 hr hzr.le hwr
  rw [diskExtension_coe, diskExtension_coe] at h
  rw [dist_eq_norm, norm_sub_rev]
  refine h.trans_lt ?_
  change C * ‖(w : ℂ) - z‖ < ε
  simpa only [mul_comm] using (lt_div_iff₀ hC).mp (hw'.trans_le (min_le_right _ _))

lemma isClosed_diskNormalized : IsClosed {f : C(UnitDisk, ℂ) | DiskNormalized f} := by
  rw [isClosed_iff_forall_filter]
  intro f l hl hs ht
  let : l.NeBot := hl
  have hlim := diskExtension_tendsto (show Tendsto id l (𝓝 f) from ht)
  have hn : ∀ᶠ g in l, DiskNormalized g := le_principal_iff.mp hs
  have hd : ∀ᶠ g in l, DifferentiableOn ℂ (diskExtension g) (ball 0 1) :=
    hn.mono (fun _ hg => hg.1)
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have h0 : diskExtension f 0 = 0 := by
    apply tendsto_nhds_unique (hlim.tendsto_at hz)
    exact tendsto_const_nhds.congr' (hn.mono fun _ hg => hg.2.2.1.symm)
  have h1 : deriv (diskExtension f) 0 = 1 := by
    apply tendsto_nhds_unique ((hlim.deriv hd isOpen_ball).tendsto_at hz)
    exact tendsto_const_nhds.congr' (hn.mono fun _ hg => hg.2.2.2.symm)
  refine ⟨hlim.differentiableOn hd isOpen_ball, ?_, h0, h1⟩
  apply locallyUniformLimit_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    hz hlim hd (hn.mono fun _ hg => hg.2.1)
  simp only [h1, ne_eq, one_ne_zero, not_false_eq_true]

lemma isCompact_diskNormalized : IsCompact {f : C(UnitDisk, ℂ) | DiskNormalized f} := by
  let : T2Space (UniformOnFun UnitDisk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (Set.eq_univ_iff_forall.mpr fun z =>
      mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have he : Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
      C(UnitDisk, ℂ) → UniformOnFun UnitDisk ℂ {K | IsCompact K}) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(UnitDisk, ℂ) => (f : UnitDisk → ℂ))
    (𝔖 := {K | IsCompact K}) (fun _ hK => hK) he
    (s := {f | DiskNormalized f})
    (fun K _ => disk_family_equicontinuous.equicontinuousOn K)
    (by
      intro K _ z _
      obtain ⟨R, hR⟩ := disk_family_pointwise_bounded z
      refine ⟨closedBall 0 R, isCompact_closedBall _ _, ?_⟩
      intro f hf
      simpa only [mem_closedBall, dist_zero_right] using hR ⟨f, hf⟩)
  rwa [isClosed_diskNormalized.closure_eq] at hc

instance : CompactSpace DiskFamily := isCompact_iff_compactSpace.mp isCompact_diskNormalized

instance : TopologicalSpace.MetrizableSpace DiskFamily :=
  TopologicalSpace.MetrizableSpace.subtype {f : C(UnitDisk, ℂ) | DiskNormalized f}

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

abbrev DiskHolomorphic := {f : C(UnitDisk, ℂ) //
  DifferentiableOn ℂ (diskExtension f) (ball 0 1)}

def diskDerivative (f : DiskHolomorphic) : C(UnitDisk, ℂ) :=
  ⟨fun z => deriv (diskExtension f.val) z,
    (f.property.deriv isOpen_ball).continuousOn.comp_continuous
      continuous_subtype_val (fun z => z.property)⟩

lemma continuous_diskDerivative : Continuous diskDerivative := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
  have h := diskExtension_tendsto (continuous_subtype_val.tendsto f)
  have hd := h.deriv (Eventually.of_forall fun g : DiskHolomorphic => g.property) isOpen_ball
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hd
  exact hd

lemma continuous_diskDerivative_eval :
    Continuous (fun p : DiskHolomorphic × UnitDisk => deriv (diskExtension p.1.val) p.2) := by
  exact continuous_diskDerivative.comp continuous_fst |>.eval continuous_snd

lemma continuous_diskFamily_derivative :
    Continuous (fun p : DiskFamily × UnitDisk => deriv (diskExtension p.1.val) p.2) := by
  exact continuous_diskDerivative_eval.comp
    ((continuous_subtype_val.subtype_mk (fun f => f.property.1)).comp continuous_fst |>.prodMk continuous_snd)

lemma diskFamily_derivative_ne_zero (f : DiskFamily) (z : UnitDisk) :
    deriv (diskExtension f.val) z ≠ 0 := by
  exact deriv_ne_zero_of_injOn isOpen_ball z.property f.property.2.1 f.property.1

end
end StrictInverseFirstPower

end

end OAI
