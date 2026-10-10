/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import OAI.Analysis.HotSpots.Conformal

namespace OAI

section RiemannBiholomorphic





noncomputable section
open Set Filter Metric Complex Function
open scoped Topology
namespace Complex
open scoped _root_.Complex












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


  rcases _root_.Complex.exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
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
    rw [mem_ball_zero_iff, norm_div, _root_.Complex.norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
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

end Complex

namespace StrictHotSpots.Riemann

variable {U : Set ℂ}


def extend (f : C(U,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then f ⟨z,hz⟩ else 0

@[simp] lemma extend_coe (f : C(U,ℂ)) (z : U) : extend f z=f z := by
  simp [extend,z.property]

lemma extend_eq (f : C(U,ℂ)) {z : ℂ} (hz : z ∈ U) : extend f z=f ⟨z,hz⟩ := by
  simp [extend,hz]

lemma extend_continuousOn (f : C(U,ℂ)) : ContinuousOn (extend f) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : U => extend f z)
  simpa only [extend_coe] using f.continuous

def holomorphicBall (U : Set ℂ) : Set C(U,ℂ) :=
  {f | DifferentiableOn ℂ (extend f) U ∧ ∀ z : U, ‖f z‖ ≤ 1}

lemma tendsto_extend {ι : Type*} {l : Filter ι} [LocallyCompactSpace U]
    {F : ι → C(U,ℂ)} {f : C(U,ℂ)} (h : Tendsto F l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => extend (F i)) (extend f) l U := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def,extend_coe] using
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h)

lemma holomorphicBall_isClosed (ho : IsOpen U) : IsClosed (holomorphicBall U) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  rw [isClosed_iff_forall_filter]
  intro f l hl hF hf
  let := hl
  have hF : ∀ᶠ g in l, g ∈ holomorphicBall U := le_principal_iff.mp hF
  refine ⟨(tendsto_extend (show Tendsto id l (𝓝 f) from hf)).differentiableOn (hF.mono fun _ hi => hi.1) ho,?_⟩
  intro z
  have hh : Tendsto (fun i => ‖i z‖) l (𝓝 ‖f z‖) :=
    by simpa only [extend_coe,id] using
      ((tendsto_extend (show Tendsto id l (𝓝 f) from hf)).tendsto_at z.property).norm
  exact le_of_tendsto hh (hF.mono fun _ hi => hi.2 z)

lemma holomorphicBall_dist_bound (_ho : IsOpen U) {f : C(U,ℂ)}
    (hf : f ∈ holomorphicBall U) {x : U} {r : ℝ} (_hr : 0 < r)
    (hball : ball (x:ℂ) r ⊆ U) {y : U} (hy : dist (y:ℂ) x < r) :
    dist (f x) (f y) ≤ (2/r)*dist (x:ℂ) y := by
  have hm : MapsTo (extend f) (ball (x:ℂ) r) (closedBall (extend f x) 2) := by
    intro z hz
    have hzu := hball hz
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖extend f z-extend f x‖ ≤ ‖extend f z‖+‖extend f x‖ := norm_sub_le _ _
      _ ≤ 1+1 := add_le_add (by simpa only [extend_eq f hzu] using hf.2 ⟨z,hzu⟩)
        (by simpa only [extend_coe,id] using hf.2 x)
      _ = 2 := by norm_num
  have hh := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hf.1.mono hball) hm
    (show (y:ℂ) ∈ ball (x:ℂ) r from hy)
  simpa only [extend_coe,dist_comm] using hh

lemma holomorphicBall_equicontinuous (ho : IsOpen U) :
    Equicontinuous (fun f : holomorphicBall U => (f.val : U → ℂ)) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨r,hr,hru⟩ := Metric.isOpen_iff.mp ho (x:ℂ) x.property
  refine ⟨min r (ε*r/2),lt_min hr (by positivity),?_⟩
  intro y hy f
  have hyr : dist (y:ℂ) x < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hye : dist (y:ℂ) x < ε*r/2 := lt_of_lt_of_le hy (min_le_right _ _)
  apply (holomorphicBall_dist_bound ho f.property hr hru hyr).trans_lt
  rw [dist_comm]
  exact (mul_lt_mul_of_pos_left hye (div_pos (by norm_num) hr)).trans_eq (by field_simp)

lemma holomorphicBall_isCompact (ho : IsOpen U) : IsCompact (holomorphicBall U) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  have : T2Space (UniformOnFun U ℂ {K : Set U | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      rw [sUnion_eq_univ_iff]
      intro x
      exact ⟨{x},isCompact_singleton,mem_singleton x⟩)
  have hc : IsCompact (closure (holomorphicBall U)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      (fun K _ => (holomorphicBall_equicontinuous ho).equicontinuousOn K)
      (fun K _ x _ => ⟨closedBall (0:ℂ) 1,isCompact_closedBall _ _,fun f hf => by
        simpa only [mem_closedBall,dist_zero_right] using hf.2 x⟩)
  simpa only [(holomorphicBall_isClosed ho).closure_eq] using hc

lemma deriv_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] (ho : IsOpen U)
    {F : ι → C(U,ℂ)} {f : C(U,ℂ)} (hF : ∀ᶠ i in l, F i ∈ holomorphicBall U)
    (hf : Tendsto F l (𝓝 f)) (z : U) :
    Tendsto (fun i => deriv (extend (F i)) z) l (𝓝 (deriv (extend f) z)) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  exact ((tendsto_extend hf).deriv (hF.mono fun _ hi => hi.1) ho).tendsto_at z.property

end StrictHotSpots.Riemann




noncomputable section
open Set Filter Metric Complex Function
open scoped Topology
namespace StrictHotSpots.Riemann

lemma hurwitz_locally_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (ho : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U ∧ ∀ z ∈ U, F i z ≠ 0)
    {z : ℂ} (hz : z ∈ U) (hfz : f z = 0) : ∀ᶠ w in 𝓝 z, f w = 0 := by
  have hfd := hconv.differentiableOn (hF.mono fun _ hi => hi.1) ho
  rcases (hfd.analyticOnNhd ho z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact h
  obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp ho z hz
  obtain ⟨δ,hδ,hδf⟩ := Metric.mem_nhdsWithin_iff.mp h
  let r := min R δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith [min_le_left R δ]
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_right R δ]
  have hcl : closedBall z r ⊆ U := (closedBall_subset_ball hrR).trans hRU
  have hs : sphere z r ⊆ U := sphere_subset_closedBall.trans hcl
  have hfs : ∀ w ∈ sphere z r, f w ≠ 0 := by
    intro w hw
    apply hδf
    refine ⟨?_,?_⟩
    · rw [mem_ball,mem_sphere.mp hw]; exact hrδ
    · simpa only [mem_compl_iff,mem_singleton_iff] using (ne_of_mem_sphere hw hr.ne')
  obtain ⟨v,hv,hvm⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (hfd.continuousOn.mono hs).norm
  let m := ‖f v‖
  have hm : 0 < m := norm_pos_iff.mpr (hfs v hv)
  have he : ∀ᶠ i in l, ∀ w ∈ sphere z r, dist (f w) (F i w) < m/2 :=
    Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact ho).mp hconv
        _ hs (isCompact_sphere z r)) _ (by positivity)
  have hbound : ∀ᶠ i in l, 1 ≤ (2/m)*‖F i z‖ := by
    filter_upwards [hF,he] with i hi hei
    have hiinv := hi.1.inv hi.2
    have hnorm : ‖(F i z)⁻¹‖ ≤ 2/m :=
      Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
        (hiinv.diffContOnCl_ball hcl) (fun w hw => by
          rw [frontier_ball z hr.ne'] at hw
          have hmin : m ≤ ‖f w‖ := hvm hw
          have hd := norm_sub_norm_le (f w) (F i w)
          have hew := hei w hw
          rw [dist_eq_norm] at hew
          have hlow : m/2 ≤ ‖F i w‖ := by linarith
          rw [Pi.inv_apply,norm_inv,inv_eq_one_div]
          calc
            1/‖F i w‖ ≤ 1/(m/2) := one_div_le_one_div_of_le (by positivity) hlow
            _ = 2/m := by field_simp)
        (by rw [closure_ball z hr.ne']; exact mem_closedBall_self hr.le)
    rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr (hi.2 z hz))] at hnorm
    exact hnorm
  have ht : Tendsto (fun i => (2/m)*‖F i z‖) l (𝓝 0) := by
    simpa only [hfz,norm_zero,mul_zero] using (hconv.tendsto_at hz).norm.const_mul (2/m)
  have hcontra : (1:ℝ) ≤ 0 := ge_of_tendsto ht hbound
  norm_num at hcontra

lemma hurwitz_injective {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U ∧ InjOn (F i) U)
    (hf : ∃ a ∈ U, ∃ b ∈ U, f a ≠ f b) : InjOn f U := by
  intro x hx y hy hxy
  by_contra hne
  have hfd := hconv.differentiableOn (hF.mono fun _ hi => hi.1) ho
  have hcst : TendstoLocallyUniformlyOn (fun i (_ : ℂ) => F i x) (fun _ => f x) l U :=
    (hconv.tendsto_at hx).tendstoUniformlyOn_const U |>.tendstoLocallyUniformlyOn
  have hsub : TendstoLocallyUniformlyOn (fun i z => F i z-F i x)
      (fun z => f z-f x) l (U \ {x}) := (hconv.sub hcst).mono sdiff_subset
  have hloc : ∀ᶠ w in 𝓝 y, f w-f x=0 := hurwitz_locally_zero
      (ho.sdiff isClosed_singleton) hsub
      (hF.mono fun i hi => ⟨(hi.1.sub_const _).mono sdiff_subset,by
        intro z hz
        exact sub_ne_zero.mpr (fun hh => hz.2 (hi.2 hz.1 hx hh))⟩)
      ⟨hy,fun hyx => hne (Eq.symm (mem_singleton_iff.mp hyx))⟩ (sub_eq_zero.mpr hxy.symm)
  have he : EqOn (fun z => f z-f x) 0 U :=
    ((hfd.sub_const _).analyticOnNhd ho).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hy hloc
  obtain ⟨a,ha,b,hb,hab⟩ := hf
  exact hab ((sub_eq_zero.mp (he ha)).trans (sub_eq_zero.mp (he hb)).symm)

end StrictHotSpots.Riemann

namespace StrictHotSpots.Riemann

def normalizedMaps {U : Set ℂ} (a : U) : Set C(U,ℂ) :=
  {f | f ∈ holomorphicBall U ∧ f a=0 ∧ (Injective f ∨ f=0)}

lemma normalizedMaps_isClosed {U : Set ℂ} (ho : IsOpen U)
    (hc : IsPreconnected U) (a : U) : IsClosed (normalizedMaps a) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  rw [isClosed_iff_forall_filter]
  intro f l hl hF hf
  let := hl
  have hF : ∀ᶠ g in l, g ∈ normalizedMaps a := le_principal_iff.mp hF
  have ht : TendstoLocallyUniformlyOn (fun g => extend g) (extend f) l U := tendsto_extend hf
  have hfa : f a=0 := by
    apply isClosed_singleton.mem_of_tendsto (by simpa only [extend_coe] using ht.tendsto_at a.property)
    exact hF.mono fun _ hg => hg.2.1
  refine ⟨(holomorphicBall_isClosed ho).mem_of_tendsto hf (hF.mono fun _ hg => hg.1),hfa,?_⟩
  by_cases hfzero : f=0
  · exact Or.inr hfzero
  left
  obtain ⟨b,hb⟩ : ∃ b : U, f b≠0 := by
    by_contra hh
    simp only [not_exists,not_not] at hh
    exact hfzero (ContinuousMap.ext hh)
  have hFb : ∀ᶠ g in l, g b≠0 := by
    exact (show Tendsto (fun g : C(U,ℂ) => g b) l (𝓝 (f b)) from
      by simpa only [extend_coe] using ht.tendsto_at b.property).eventually
        (show ∀ᶠ z in 𝓝 (f b), z ≠ 0 from isOpen_compl_singleton.mem_nhds hb)
  have hin : InjOn (extend f) U := hurwitz_injective ho hc ht
    (by
      filter_upwards [hF,hFb] with g hg hgb
      refine ⟨hg.1.1,?_⟩
      have hgInj : Injective g := hg.2.2.resolve_right (by intro hg0; simp [hg0] at hgb)
      intro x hx y hy hxy
      exact congrArg Subtype.val (hgInj (by simpa only [extend_eq g hx,extend_eq g hy] using hxy)))
    ⟨b,b.property,a,a.property,by simpa only [extend_coe,hfa] using hb⟩
  intro x y hxy
  exact Subtype.ext (hin x.property y.property (by simpa only [extend_coe] using hxy))

lemma normalizedMaps_isCompact {U : Set ℂ} (ho : IsOpen U)
    (hc : IsPreconnected U) (a : U) : IsCompact (normalizedMaps a) :=
  (holomorphicBall_isCompact ho).of_isClosed_subset (normalizedMaps_isClosed ho hc a)
    (fun _ hf => hf.1)

lemma deriv_continuousOn {U : Set ℂ} (ho : IsOpen U) (a : U) :
    ContinuousOn (fun f : C(U,ℂ) => deriv (extend f) a) (holomorphicBall U) := by
  rw [continuousOn_iff_continuous_domRestrict,continuous_iff_continuousAt]
  intro f
  exact deriv_tendsto ho (Eventually.of_forall fun g : holomorphicBall U => g.property)
    continuous_subtype_val.continuousAt a

lemma exists_extremal {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U) (a : U)
    {g : C(U,ℂ)} (hg : g ∈ normalizedMaps a) (hgd : deriv (extend g) a ≠ 0) :
    ∃ f ∈ normalizedMaps a, 0 < ‖deriv (extend f) a‖ ∧
      ∀ h ∈ normalizedMaps a, ‖deriv (extend h) a‖ ≤ ‖deriv (extend f) a‖ := by
  obtain ⟨f,hf,hmax⟩ := (normalizedMaps_isCompact ho hc a).exists_isMaxOn ⟨g,hg⟩
    ((deriv_continuousOn ho a).mono (fun _ hh => hh.1)).norm
  exact ⟨f,hf,(norm_pos_iff.mpr hgd).trans_le (hmax hg),hmax⟩


lemma extend_eventuallyEq {U : Set ℂ} (ho : IsOpen U) (g : C(U,ℂ))
    {f : ℂ → ℂ} (hf : ∀ z : U, g z=f z) (a : U) :
    extend g =ᶠ[𝓝 (a:ℂ)] f := by
  filter_upwards [ho.mem_nhds a.property] with z hz
  rw [extend_eq g hz]
  exact hf ⟨z,hz⟩

lemma normalized_initial {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) :
    ∃ g ∈ normalizedMaps a, deriv (extend g) a ≠ 0 := by
  obtain ⟨f,hfmap,hfinj,hfderiv⟩ := Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero ho hs hU
  have hfd : DifferentiableOn ℂ f U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hfderiv z hz)).differentiableWithinAt
  let g : C(U,ℂ) := ⟨fun z => (f z-f a)/2,
    hfd.continuousOn.domRestrict.sub continuous_const |>.div_const 2⟩
  have heq : ∀ z ∈ U, extend g z = (f z-f a)/2 := fun z hz => extend_eq g hz
  refine ⟨g,⟨⟨((hfd.sub_const _).div_const 2).congr heq,?_⟩,?_,Or.inl ?_⟩,?_⟩
  · intro z
    change ‖(f z-f a)/2‖ ≤ 1
    rw [norm_div,Complex.norm_ofNat,div_le_one₀ (by norm_num : (0:ℝ)<2)]
    exact (norm_sub_le _ _).trans (by
      have hz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hfmap z.property)
      have ha : ‖f a‖ < 1 := mem_ball_zero_iff.mp (hfmap a.property)
      linarith)
  · change (f a-f a)/2=0
    simp
  · intro x y hxy
    apply Subtype.ext
    apply hfinj x.property y.property
    change (f x-f a)/2=(f y-f a)/2 at hxy
    have h2 : f x-f a=f y-f a := (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp hxy
    linear_combination h2
  · rw [(extend_eventuallyEq ho g (f := fun z => (f z-f a)/2) (fun _ => rfl) a).deriv_eq,deriv_div_const,
      deriv_sub_const]
    exact div_ne_zero (hfderiv a a.property) (by norm_num)

lemma exists_nonzero_extremal {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) :
    ∃ f ∈ normalizedMaps a, 0 < ‖deriv (extend f) a‖ ∧
      ∀ h ∈ normalizedMaps a, ‖deriv (extend h) a‖ ≤ ‖deriv (extend f) a‖ := by
  obtain ⟨g,hg,hgd⟩ := normalized_initial ho hs hU a
  have hc : IsPreconnected U := hs.isPathConnected.isConnected.isPreconnected
  exact exists_extremal ho hc a hg hgd

lemma normalized_norm_lt {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    (a : U) {f : C(U,ℂ)} (hf : f ∈ normalizedMaps a) (z : U) : ‖f z‖ < 1 := by
  by_contra hle
  have heq : ‖f z‖=1 := le_antisymm (hf.1.2 z) (not_lt.mp hle)
  have hmax : IsMaxOn (norm ∘ extend f) U (z:ℂ) := by
    intro w hw
    change ‖extend f w‖ ≤ ‖extend f z‖
    rw [extend_eq f hw,extend_coe,heq]
    exact hf.1.2 ⟨w,hw⟩
  have hh := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hf.1.1 z.property hmax a.property
  simp only [extend_coe,Function.const_apply,hf.2.1] at hh
  rw [← hh,norm_zero] at heq
  norm_num at heq

end StrictHotSpots.Riemann




noncomputable section
open Set Filter Metric Complex Function
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

def mobius (a z : ℂ) : ℂ := (z-a)/(1-conj a*z)

lemma mobius_denom_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1-conj a*z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hh : ‖conj a*z‖ < 1 := by
    rw [norm_mul,norm_conj]
    nlinarith [norm_nonneg a,norm_nonneg z]
  rw [← he,norm_one] at hh
  exact lt_irrefl _ hh

lemma mobius_norm_identity (a z : ℂ) :
    ‖1-conj a*z‖^2-‖z-a‖^2=(1-‖a‖^2)*(1-‖z‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,sub_re,sub_im,
    one_re,one_im,mul_re,mul_im,conj_re,conj_im]
  ring

lemma norm_mobius_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖mobius a z‖ < 1 := by
  have hden : 0 < ‖1-conj a*z‖ := norm_pos_iff.mpr (mobius_denom_ne ha hz)
  rw [mobius,norm_div,div_lt_one₀ hden]
  have hpos : 0 < (1-‖a‖^2)*(1-‖z‖^2) := mul_pos
    (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hh := mobius_norm_identity a z
  nlinarith [norm_nonneg (z-a)]

@[simp] lemma mobius_self (a : ℂ) : mobius a a=0 := by simp [mobius]
@[simp] lemma mobius_zero (a : ℂ) : mobius a 0 = -a := by simp [mobius]

lemma mobius_injOn {a : ℂ} (ha : ‖a‖ < 1) : InjOn (mobius a) (ball 0 1) := by
  intro x hx y hy he
  have hx' := mobius_denom_ne ha (mem_ball_zero_iff.mp hx)
  have hy' := mobius_denom_ne ha (mem_ball_zero_iff.mp hy)
  have haa := mobius_denom_ne ha ha
  have hcross := (div_eq_div_iff hx' hy').mp he
  have hmul : (x-y)*(1-conj a*a)=0 := by linear_combination hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right haa)

lemma hasDerivAt_mobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mobius a) ((1-conj a*a)/(1-conj a*z)^2) z := by
  have hh := ((hasDerivAt_id z).sub_const a).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (conj a))) (mobius_denom_ne ha hz)
  change HasDerivAt (fun w => (w-a)/(1-conj a*w))
    ((1*(1-conj a*z)-(z-a)*(0-conj a*1))/(1-conj a*z)^2) z at hh
  have he : 1*(1-conj a*z)-(z-a)*(0-conj a*1)=1-conj a*a := by ring
  rw [he] at hh
  exact hh

lemma hasDerivAt_mobius_zero {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (mobius a) (1-conj a*a) 0 := by
  simpa using hasDerivAt_mobius ha (by simp : ‖(0:ℂ)‖<1)

lemma norm_mobius_self_deriv {a : ℂ} (ha : ‖a‖ < 1) :
    ‖(1-conj a*a)/(1-conj a*a)^2‖=1/(1-‖a‖^2) := by
  have hh : 0 < 1-‖a‖^2 := by nlinarith [norm_nonneg a]
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  norm_cast
  rw [norm_div,norm_pow,Real.norm_of_nonneg hh.le]
  field_simp

lemma norm_mobius_zero_deriv {a : ℂ} (ha : ‖a‖ < 1) :
    ‖1-conj a*a‖=1-‖a‖^2 := by
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  norm_cast
  exact Real.norm_of_nonneg (by nlinarith [norm_nonneg a])

lemma hasDerivAt_continuous_square_root {r h : ℂ → ℂ} {a d : ℂ}
    (hrc : ContinuousAt r a) (hr : r a ≠ 0) (he : ∀ z, r z^2=h z)
    (hh : HasDerivAt h d a) : HasDerivAt r ((2*r a)⁻¹*d) a := by
  have hq : HasStrictDerivAt (fun z : ℂ => z^2) (2*r a) (r a) := by
    simpa using hasStrictDerivAt_pow 2 (r a)
  have hqne : 2*r a ≠ 0 := mul_ne_zero (by norm_num) hr
  let k := hq.localInverse (fun z : ℂ => z^2) (2*r a) (r a) hqne
  have hk : HasDerivAt k (2*r a)⁻¹ (h a) := by
    rw [← he a]
    exact (hq.to_localInverse hqne).hasDerivAt
  have hke : (fun z => k (h z)) =ᶠ[𝓝 a] r := by
    have hev := hrc.eventually (hq.eventually_left_inverse hqne)
    filter_upwards [hev] with z hz
    simpa only [he] using hz
  exact (hk.comp a hh).congr_of_eventuallyEq hke.symm


lemma root_improvement_inequality {r d : ℝ} (hr : 0 < r) (hr1 : r < 1) (hd : 0 < d) :
    d < (1/(1-r^2)) * ((2*r)⁻¹*((1-(r^2)^2)*d)) := by
  have hp : 0 < 1-r^2 := by nlinarith
  have he : (1/(1-r^2)) * ((2*r)⁻¹*((1-(r^2)^2)*d)) =
      (1+r^2)/(2*r)*d := by
    field_simp
    ring
  rw [he]
  have hh : 1 < (1+r^2)/(2*r) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)])
  simpa using mul_lt_mul_of_pos_right hh hd




lemma exists_root_improvement {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hfm : ∀ z ∈ U, ‖f z‖ < 1) (hfa : f a = 0)
    (hdf : 0 < ‖deriv f a‖) {c : ℂ} (hc : ‖c‖ < 1) (hcf : c ∉ f '' U) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ InjOn g U ∧
      (∀ z ∈ U, ‖g z‖ < 1) ∧ g a=0 ∧ ‖deriv f a‖ < ‖deriv g a‖ := by
  have hdc (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w => mobius c (f w))
      (((1-conj c*c)/(1-conj c*f z)^2)*deriv f z) z :=
    (hasDerivAt_mobius hc (hfm z hz)).comp z ((hfd z hz).differentiableAt (ho.mem_nhds hz)).hasDerivAt
  have hcn (z : ℂ) (hz : z ∈ U) : mobius c (f z) ≠ 0 := by
    rw [mobius,div_ne_zero_iff]
    exact ⟨sub_ne_zero.mpr (by intro he; exact hcf ⟨z,hz,he⟩),mobius_denom_ne hc (hfm z hz)⟩
  obtain ⟨r,hrc,hreq⟩ := Complex.exists_continuousOn_pow_eq hs ho
    (show ContinuousOn (fun z => mobius c (f z)) U from fun z hz => (hdc z hz).continuousAt.continuousWithinAt)
    (by rintro ⟨z,hz,he⟩; exact hcn z hz he) two_ne_zero
  have hrn (z : ℂ) (hz : z ∈ U) : r z ≠ 0 := by
    intro he
    have hh := hreq z
    rw [he,zero_pow two_ne_zero] at hh
    exact hcn z hz hh.symm
  have hrm (z : ℂ) (hz : z ∈ U) : ‖r z‖ < 1 := by
    have hh := congrArg norm (hreq z)
    rw [norm_pow] at hh
    have hlt := norm_mobius_lt hc (hfm z hz)
    nlinarith [norm_nonneg (r z)]
  have hrd (z : ℂ) (hz : z ∈ U) : HasDerivAt r
      ((2*r z)⁻¹ * (((1-conj c*c)/(1-conj c*f z)^2)*deriv f z)) z :=
    hasDerivAt_continuous_square_root (hrc.continuousAt (ho.mem_nhds hz)) (hrn z hz) hreq (hdc z hz)
  have hri : InjOn r U := by
    intro x hx y hy he
    apply hfi hx hy
    apply mobius_injOn hc (mem_ball_zero_iff.mpr (hfm x hx)) (mem_ball_zero_iff.mpr (hfm y hy))
    rw [← hreq x,← hreq y,he]
  let g : ℂ → ℂ := fun z => mobius (r a) (r z)
  have hgd (z : ℂ) (hz : z ∈ U) : HasDerivAt g
      (((1-conj (r a)*r a)/(1-conj (r a)*r z)^2)*
        ((2*r z)⁻¹ * (((1-conj c*c)/(1-conj c*f z)^2)*deriv f z))) z :=
    (hasDerivAt_mobius (hrm a ha) (hrm z hz)).comp z (hrd z hz)
  refine ⟨g,(fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt),?_,?_,?_,?_⟩
  · intro x hx y hy he
    exact hri hx hy (mobius_injOn (hrm a ha) (mem_ball_zero_iff.mpr (hrm x hx))
      (mem_ball_zero_iff.mpr (hrm y hy)) he)
  · intro z hz
    exact norm_mobius_lt (hrm a ha) (hrm z hz)
  · exact mobius_self _
  · have hnorm : ‖c‖=‖r a‖^2 := by
      have hh := congrArg norm (hreq a)
      simpa only [hfa,mobius_zero,norm_pow,norm_neg] using hh.symm
    rw [(hgd a ha).deriv,norm_mul,norm_mobius_self_deriv (hrm a ha),norm_mul,
      norm_inv,norm_mul,Complex.norm_ofNat,norm_mul,hfa]
    simp only [mul_zero,sub_zero,one_pow,div_one]
    rw [norm_mobius_zero_deriv hc,hnorm]
    exact root_improvement_inequality (norm_pos_iff.mpr (hrn a ha)) (hrm a ha) hdf

end StrictHotSpots.Riemann

namespace StrictHotSpots.Riemann


lemma exists_normalized_bijective {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) :
    ∃ f : ℂ → ℂ, f a=0 ∧ BijOn f U (ball 0 1) ∧ DifferentiableOn ℂ f U ∧
      0 < ‖deriv f a‖ := by
  obtain ⟨f,hf,hd,hmax⟩ := exists_nonzero_extremal ho hs hU a
  have hfinj : Injective f := hf.2.2.resolve_right (by
    intro he
    subst f
    have hezero : extend (0:C(U,ℂ))=0 := by ext z; simp [extend]
    rw [hezero] at hd
    simp at hd)
  have hfi : InjOn (extend f) U := by
    intro x hx y hy he
    exact congrArg Subtype.val (hfinj (by simpa only [extend_eq f hx,extend_eq f hy] using he))
  have hfm : ∀ z ∈ U, ‖extend f z‖ < 1 := by
    intro z hz
    rw [extend_eq f hz]
    exact normalized_norm_lt ho hs.isPathConnected.isConnected.isPreconnected a hf ⟨z,hz⟩
  have hfa : extend f a=0 := by simpa only [extend_coe] using hf.2.1
  refine ⟨extend f,hfa,⟨(fun z hz => mem_ball_zero_iff.mpr (hfm z hz)),hfi,?_⟩,hf.1.1,hd⟩
  intro c hc
  by_contra hcf
  obtain ⟨g,hgd,hgi,hgm,hga,hbetter⟩ := exists_root_improvement ho hs a.property hf.1.1 hfi hfm hfa hd
    (mem_ball_zero_iff.mp hc) hcf
  let G : C(U,ℂ) := ⟨U.domRestrict g,hgd.continuousOn.domRestrict⟩
  have hG : G ∈ normalizedMaps a := by
    refine ⟨⟨hgd.congr (fun z hz => extend_eq G hz),?_⟩,hga,Or.inl ?_⟩
    · intro z
      exact (hgm z z.property).le
    · intro x y he
      exact Subtype.ext (hgi x.property y.property he)
  have hh := hmax G hG
  rw [(extend_eventuallyEq ho G (f:=g) (fun _ => rfl) a).deriv_eq] at hh
  exact (not_lt_of_ge hh) hbetter

end StrictHotSpots.Riemann





noncomputable section
open Set Filter Metric Complex Function
open scoped Topology
namespace StrictHotSpots.Riemann

lemma analytic_inverse_openPartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ)
    (hc : IsPreconnected e.source) (hd : DifferentiableOn ℂ e e.source)
    {a : ℂ} (ha : a ∈ e.source) (hda : deriv e a ≠ 0) :
    DifferentiableOn ℂ e.symm e.target ∧ ∀ x ∈ e.source, deriv e x ≠ 0 := by
  have han := hd.analyticOnNhd e.open_source
  have hinv (x : ℂ) (hx : x ∈ e.source) : AnalyticAt ℂ e.symm (e x) := by
    have hdn : ∀ᶠ z in 𝓝[≠] x, deriv e z ≠ 0 := by
      rcases (han.deriv x hx).eventually_eq_zero_or_eventually_ne_zero with he | he
      · have hzero := han.deriv.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc hx he
        exact (hda (hzero ha)).elim
      · exact he
    have ht : Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] x) := by
      have ht0 : Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] e.symm (e x)) :=
        tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt_symm (e.map_source hx)).tendsto.mono_left nhdsWithin_le_nhds,
          e.symm.eventually_ne_nhdsWithin (e.map_source hx)⟩
      simpa only [e.left_inv hx] using ht0
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ (e.continuousAt_symm (e.map_source hx))
    filter_upwards [ht.eventually hdn,eventually_nhdsWithin_of_eventually_nhds
      (e.open_target.mem_nhds (e.map_source hx))] with y hdy hy
    exact (e.hasDerivAt_symm hy hdy
      ((hd (e.symm y) (e.map_target hy)).differentiableAt
        (e.open_source.mem_nhds (e.map_target hy))).hasDerivAt).differentiableAt
  refine ⟨?_,?_⟩
  · intro y hy
    have hh := hinv (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at hh
    exact hh.differentiableAt.differentiableWithinAt
  · intro x hx
    have hcomp := (hinv x hx).differentiableAt.hasDerivAt.comp x
      ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasDerivAt
    have heq : deriv e.symm (e x) * deriv e x = 1 :=
      hcomp.unique ((hasDerivAt_id x).congr_of_eventuallyEq (e.eventually_left_inverse hx))
    intro he
    rw [he,mul_zero] at heq
    exact zero_ne_one heq

lemma exists_biholomorphic_inverse {U V : Set ℂ} (ho : IsOpen U)
    (hc : IsPreconnected U) {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f U)
    (hfb : BijOn f U V) {a : ℂ} (ha : a ∈ U) (hda : deriv f a ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ)=f ∧ e.source=U ∧ e.target=V ∧
      DifferentiableOn ℂ e.symm V ∧ (∀ x ∈ U, deriv f x ≠ 0) := by
  have hop : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    rcases (hfd.analyticOnNhd ho).is_constant_or_isOpen hc with h | h
    · obtain ⟨c,he⟩ := h
      have hg : f =ᶠ[𝓝 a] fun _ => c := by
        filter_upwards [ho.mem_nhds ha] with z hz
        exact he z hz
      exact (hda (by rw [hg.deriv_eq,deriv_const])).elim
    · exact h
  have hrestrict : IsOpenMap (U.domRestrict f) := by
    intro s hs
    have hsub : Subtype.val '' s ⊆ U := by rintro _ ⟨x,_,rfl⟩; exact x.property
    change IsOpen ((fun x : U => f x) '' s)
    simpa only [image_image,comp_def] using hop (Subtype.val '' s) hsub (ho.isOpenMap_subtype_val s hs)
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict (hfb.toPartialEquiv f U V)
    hfd.continuousOn hrestrict ho
  have he : (e : ℂ → ℂ)=f := rfl
  have hes : e.source=U := rfl
  have het : e.target=V := rfl
  have hh := analytic_inverse_openPartialHomeomorph e hc hfd ha hda
  exact ⟨e,he,hes,het,hh.1,hh.2⟩

end StrictHotSpots.Riemann


namespace StrictHotSpots.Riemann



theorem exists_disk_biholomorphism {U : Set ℂ} (ho : IsOpen U)
    (hs : IsSimplyConnected U) (hne : U.Nonempty) (hU : U ≠ univ) :
    ∃ Φ : OpenPartialHomeomorph ℂ ℂ, Φ.source = ball 0 1 ∧ Φ.target = U ∧
      DifferentiableOn ℂ Φ (ball 0 1) ∧ DifferentiableOn ℂ Φ.symm U ∧
      (∀ z ∈ ball (0:ℂ) 1, deriv Φ z ≠ 0) ∧
      (∀ w ∈ U, deriv Φ.symm w ≠ 0) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨f,_,hfb,hfd,hda⟩ := exists_normalized_bijective ho hs hU ⟨a,ha⟩
  obtain ⟨e,he,hes,het,hdi,hen⟩ := exists_biholomorphic_inverse ho
    hs.isPathConnected.isConnected.isPreconnected hfd hfb ha
    (norm_pos_iff.mp hda)
  refine ⟨e.symm,het,hes,hdi,?_,?_,?_⟩
  · simpa only [e.symm_symm,he] using hfd
  · intro z hz
    have hzt : z ∈ e.target := het.symm ▸ hz
    have hw : e.symm z ∈ U := hes ▸ e.map_target hzt
    have hd : HasDerivAt e (deriv f (e.symm z)) (e.symm z) := by
      rw [he]
      exact ((hfd _ hw).differentiableAt (ho.mem_nhds hw)).hasDerivAt
    have hd' := e.hasDerivAt_symm hzt (hen _ hw) hd
    rw [hd'.deriv]
    exact inv_ne_zero (hen _ hw)
  · simpa only [e.symm_symm,he] using hen

end StrictHotSpots.Riemann
end
end
end
end
end RiemannBiholomorphic

section RiemannDomain





noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace StrictHotSpots.Conformal

lemma conjugate_contDiffOn {f : ℂ → ℂ} {U : Set ℂ}
    (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) :
    ContDiffOn ℝ ∞ (fun x : Plane => coordinate (f (coordinate.symm x)))
      (coordinate.symm ⁻¹' U) := by
  exact coordinate.contDiff.comp_contDiffOn
    (((hd.contDiffOn ho).restrict_scalars ℝ).comp coordinate.symm.contDiff.contDiffOn
      (fun _ hx => hx))

lemma conjugate_hasFDerivAt {f : ℂ → ℂ} {x : Plane}
    (hd : DifferentiableAt ℂ f (coordinate.symm x)) :
    HasFDerivAt (fun y : Plane => coordinate (f (coordinate.symm y)))
      (planeMul (deriv f (coordinate.symm x))) x :=
  coordinate.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    ((hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp x
      coordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)



theorem exists_interior_chart {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (d d' : Plane → ℂ),
      e.source = DiskH10.disk ∧ e.target = Ω ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) ∧
      (∀ y ∈ e.target, HasFDerivAt e.symm (planeMul (d' y)) y) ∧
      (∀ x ∈ e.source, d x ≠ 0) ∧ (∀ y ∈ e.target, d' y ≠ 0) := by
  let U : Set ℂ := coordinate ⁻¹' Ω
  have hUo : IsOpen U := ho.preimage coordinate.continuous
  have hUs : IsSimplyConnected U :=
    coordinate.toHomeomorph.isSimplyConnected_preimage.mpr hs
  have hUne : U.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨coordinate.symm x,by simpa [U] using hx⟩
  have hproper : U ≠ univ := by
    intro hh
    have hu : Ω = univ := by
      apply eq_univ_of_forall
      intro x
      have hx : coordinate.symm x ∈ U := hh ▸ mem_univ _
      simpa [U] using hx
    exact NormedSpace.unbounded_univ ℝ Plane (hu ▸ hb)
  obtain ⟨Φ,hΦs,hΦt,hΦ,hΦi,hd,hd'⟩ :=
    Riemann.exists_disk_biholomorphism hUo hUs hUne hproper
  let e := planeChart Φ
  have hes : e.source = DiskH10.disk := by
    rw [planeChart_source,hΦs]
    ext x
    simp only [mem_preimage,mem_ball,dist_zero_right,coordinate.symm.norm_map,
      DiskH10.disk]
  have het : e.target = Ω := by
    rw [planeChart_target,hΦt]
    ext x
    simp [U]
  have heq : (e : Plane → Plane) = fun x => coordinate (Φ (coordinate.symm x)) := rfl
  have hiq : (e.symm : Plane → Plane) = fun x => coordinate (Φ.symm (coordinate.symm x)) := rfl
  have hsrc (x : Plane) (hx : x ∈ e.source) : coordinate.symm x ∈ ball (0:ℂ) 1 := by
    rwa [planeChart_source,hΦs] at hx
  have htgt (x : Plane) (hx : x ∈ e.target) : coordinate.symm x ∈ U := by
    rwa [planeChart_target,hΦt] at hx
  refine ⟨e,fun x => deriv Φ (coordinate.symm x),
    fun y => deriv Φ.symm (coordinate.symm y),hes,het,?_,?_,?_,?_,?_,?_⟩
  · rw [heq,planeChart_source,hΦs]
    exact conjugate_contDiffOn isOpen_ball hΦ
  · rw [hiq,planeChart_target,hΦt]
    exact conjugate_contDiffOn hUo hΦi
  · intro x hx
    rw [heq]
    exact conjugate_hasFDerivAt ((hΦ _ (hsrc x hx)).differentiableAt
      (isOpen_ball.mem_nhds (hsrc x hx)))
  · intro y hy
    rw [hiq]
    exact conjugate_hasFDerivAt ((hΦi _ (htgt y hy)).differentiableAt
      (hUo.mem_nhds (htgt y hy)))
  · intro x hx
    exact hd _ (hsrc x hx)
  · intro y hy
    exact hd' _ (htgt y hy)

end StrictHotSpots.Conformal
end
end RiemannDomain

section ConformalPotential





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane) (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)

include hd in
lemma chartMeasure_univ : chartMeasure e d univ = volume e.target := by
  have hh := congrArg (fun ν : Measure Plane => ν univ) (map_chartMeasure e d hd)
  rw [Measure.map_apply_of_aemeasurable (chart_aemeasurable e d) MeasurableSet.univ] at hh
  simpa only [preimage_univ,Measure.restrict_apply_univ] using hh

include hd in
lemma chartMeasure_finite (hb : Bornology.IsBounded e.target) :
    IsFiniteMeasure (chartMeasure e d) :=
  ⟨(chartMeasure_univ e d hd).trans_lt hb.measure_lt_top⟩


def potentialMeasure (μ : ℝ) : Measure Plane :=
  ENNReal.ofReal μ • chartMeasure e d

lemma potentialMeasure_density {μ : ℝ} (hμ : 0 ≤ μ) :
    potentialMeasure e d μ = (volume.restrict e.source).withDensity
      (fun x => ENNReal.ofReal (μ*‖d x‖^2)) := by
  have hh := withDensity_smul' (μ:=volume.restrict e.source) (ENNReal.ofReal μ)
    (fun x => ENNReal.ofReal (‖d x‖^2)) ENNReal.ofReal_ne_top
  simpa only [potentialMeasure,chartMeasure,Pi.smul_def,smul_eq_mul,
    ENNReal.ofReal_mul hμ] using hh.symm

lemma potentialMeasure_integral {μ : ℝ} (hμ : 0 ≤ μ) (f : Plane → ℝ) :
    (∫ x, f x ∂potentialMeasure e d μ) = μ * ∫ x, f x ∂chartMeasure e d := by
  rw [potentialMeasure,integral_smul_measure,ENNReal.toReal_ofReal hμ,smul_eq_mul]

include hd in
lemma potentialMeasure_map (μ : ℝ) :
    (potentialMeasure e d μ).map e = ENNReal.ofReal μ • volume.restrict e.target := by
  rw [potentialMeasure,Measure.map_smul _ (chart_aemeasurable e d),map_chartMeasure e d hd]

include hd in
lemma potentialMeasure_finite (μ : ℝ) (hb : Bornology.IsBounded e.target) :
    IsFiniteMeasure (potentialMeasure e d μ) := by
  let := chartMeasure_finite e d hd hb
  exact Measure.smul_finite (chartMeasure e d) ENNReal.ofReal_ne_top

lemma scale_gap {μ L A B : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (h : L*A ≤ B) : μ*A ≤ (μ/L)*B := by
  have he : μ*A = (μ/L)*(L*A) := by
    rw [← mul_assoc,div_mul_cancel₀ _ hL.ne']
  exact he ▸ mul_le_mul_of_nonneg_left h (div_pos hμ hL).le

include hd in

theorem potentialMeasure_subcritical (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hb : Bornology.IsBounded e.target) (hne : e.target.Nonempty)
    (hμ : 0 < firstPositiveNeumannValue e.target) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ v : H10 e.open_source,
        (∫ x, (H10.value e.open_source v x)^2
          ∂potentialMeasure e d (firstPositiveNeumannValue e.target)) ≤
        δ*‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (weighted_subcritical e he d hd hb hne)
  intro L h
  refine ⟨firstPositiveNeumannValue e.target/L,div_pos hμ h.1,
    (div_lt_one h.1).mpr h.2.1,fun v => ?_⟩
  rw [potentialMeasure_integral e d hμ.le]
  exact scale_gap hμ h.1 (h.2.2 v)



theorem exists_actual_subcritical_potential {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InFirstNeumannEigenspace Ω u)
    (hu0 : ∃ x ∈ Ω, u x ≠ 0) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (d d' : Plane → ℂ),
      e.source = DiskH10.disk ∧ e.target = Ω ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) ∧
      (∀ y ∈ e.target, HasFDerivAt e.symm (planeMul (d' y)) y) ∧
      (∀ x ∈ e.source, d x ≠ 0) ∧ (∀ y ∈ e.target, d' y ≠ 0) ∧
      IsFiniteMeasure (potentialMeasure e d (firstPositiveNeumannValue Ω)) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ v : H10 e.open_source,
          (∫ x, (H10.value e.open_source v x)^2
            ∂potentialMeasure e d (firstPositiveNeumannValue Ω)) ≤
          δ*‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (exists_interior_chart hΩ.2.1 hΩ.2.2.2.1 hΩ.1 hΩ.2.2.1)
  intro e h
  apply Exists.elim h
  intro d h
  apply Exists.elim h
  intro d' h
  have hes := h.1
  have het := h.2.1
  have he := h.2.2.1
  have he' := h.2.2.2.1
  have hd := h.2.2.2.2.1
  have hd' := h.2.2.2.2.2.1
  have hn := h.2.2.2.2.2.2.1
  have hn' := h.2.2.2.2.2.2.2
  have hb : Bornology.IsBounded e.target := het.symm ▸ hΩ.2.2.1
  have hne : e.target.Nonempty := het.symm ▸ hΩ.1
  have hμ : 0 < firstPositiveNeumannValue e.target :=
    het.symm ▸ firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hu0
  refine ⟨e,d,d',hes,het,he,he',hd,hd',hn,hn',
    potentialMeasure_finite e d hd _ hb,?_⟩
  have hh := potentialMeasure_subcritical e d hd he' hb hne hμ
  simpa only [het] using hh

end StrictHotSpots.Conformal
end
end ConformalPotential

section RiemannSchwarz

noncomputable section
open Set Filter Metric _root_.OAI.Complex Function
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

lemma mobius_neg_zero (z : ℂ) : mobius (-z) 0 = z := by simp


theorem schwarz_mobius_ball {f : ℂ → ℂ} {c x : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r))
    (hm : MapsTo f (ball c r) (ball 0 1)) (hx : x ∈ ball c r) :
    ‖mobius (f c) (f x)‖ ≤ dist x c / r := by
  have hr : 0 < r := nonempty_ball.mp ⟨x,hx⟩
  have hc : c ∈ ball c r := mem_ball_self hr
  have hfc : ‖f c‖ < 1 := mem_ball_zero_iff.mp (hm hc)
  let g : ℂ → ℂ := fun y => mobius (f c) (f y)
  have hg0 : g c = 0 := mobius_self _
  have hgd : DifferentiableOn ℂ g (ball c r) := by
    intro y hy
    exact ((hasDerivAt_mobius hfc (mem_ball_zero_iff.mp (hm hy))).differentiableAt.comp y
      ((hd y hy).differentiableAt (isOpen_ball.mem_nhds hy))).differentiableWithinAt
  have hgm : MapsTo g (ball c r) (closedBall (g c) 1) := by
    intro y hy
    rw [hg0,mem_closedBall_zero_iff]
    exact (norm_mobius_lt hfc (mem_ball_zero_iff.mp (hm hy))).le
  have H := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hgm hx
  simpa only [g,hg0,dist_zero_right,one_div,div_eq_mul_inv,mul_comm,mul_one] using H



theorem schwarz_pick_deriv {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖deriv f z‖ * (1-‖z‖^2) ≤ 1-‖f z‖^2 := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hm hz)
  have hneg : ‖-z‖ < 1 := by simpa only [norm_neg] using hz'
  let g : ℂ → ℂ := fun w => mobius (f z) (f (mobius (-z) w))
  have hg0 : g 0 = 0 := by simp [g]
  have hgd (w : ℂ) (hw : w ∈ ball 0 1) : DifferentiableAt ℂ g w := by
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hmw : mobius (-z) w ∈ ball 0 1 := mem_ball_zero_iff.mpr (norm_mobius_lt hneg hw')
    exact ((hasDerivAt_mobius hfz (mem_ball_zero_iff.mp (hm hmw))).differentiableAt.comp w
      (((hd _ hmw).differentiableAt (isOpen_ball.mem_nhds hmw)).comp _
        (hasDerivAt_mobius hneg hw').differentiableAt))
  have hgm : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro w hw
    rw [hg0,mem_closedBall_zero_iff]
    exact (norm_mobius_lt hfz (mem_ball_zero_iff.mp
      (hm (mem_ball_zero_iff.mpr (norm_mobius_lt hneg (mem_ball_zero_iff.mp hw)))))).le
  have hle := Complex.norm_deriv_le_one_of_mapsTo_ball
    (fun w hw => (hgd w hw).differentiableWithinAt) hgm (by norm_num : (0:ℝ)<1)
  have hdf : HasDerivAt f (deriv f z) (mobius (-z) (0:ℂ)) := by
    simpa only [mobius_neg_zero] using
      ((hd z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hinner : HasDerivAt (fun w : ℂ => f (mobius (-z) w))
      (deriv f z * (1-conj (-z)*(-z))) (0:ℂ) := by
    exact hdf.comp (0:ℂ) (hasDerivAt_mobius_zero hneg)
  have houter : HasDerivAt (mobius (f z))
      ((1-conj (f z)*f z)/(1-conj (f z)*f z)^2) (f (mobius (-z) (0:ℂ))) := by
    simpa only [mobius_neg_zero] using hasDerivAt_mobius hfz hfz
  have hd0 := houter.comp (0:ℂ) hinner
  change HasDerivAt g
    (((1-conj (f z)*f z)/(1-conj (f z)*f z)^2)*
      (deriv f z*(1-conj (-z)*(-z)))) 0 at hd0
  rw [hd0.deriv,norm_mul,norm_mul,norm_mobius_self_deriv hfz,
    norm_mobius_zero_deriv hneg,norm_neg] at hle
  have hpos : 0 < 1-‖f z‖^2 := by nlinarith [norm_nonneg (f z)]
  have hh : (‖deriv f z‖*(1-‖z‖^2))/(1-‖f z‖^2) ≤ 1 := by
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hle
  exact (div_le_one hpos).mp hh

lemma mobius_deficit_identity {a y : ℂ} (ha : ‖a‖ < 1) (hy : ‖y‖ < 1) :
    (1-‖mobius a y‖^2)*‖1-conj a*y‖^2 = (1-‖a‖^2)*(1-‖y‖^2) := by
  have hn : ‖1-conj a*y‖ ≠ 0 := norm_ne_zero_iff.mpr (mobius_denom_ne ha hy)
  rw [mobius,norm_div,div_pow]
  calc
    _ = ‖1-conj a*y‖^2-‖y-a‖^2 := by rw [sub_mul,one_mul,div_mul_cancel₀ _ (pow_ne_zero _ hn)]
    _ = _ := mobius_norm_identity a y



lemma mobius_boundary_deficit {a y : ℂ} {m t : ℝ}
    (hm : m < 1) (ha : ‖a‖ ≤ m) (hy : ‖y‖ < 1)
    (ht : t < 1) (hmt : ‖mobius a y‖ ≤ t) :
    (1-m)^2*(1-t) ≤ 2*(1-‖y‖) := by
  have ha' : ‖a‖ < 1 := ha.trans_lt hm
  have ht0 : 0 ≤ t := (norm_nonneg _).trans hmt
  have hm0 : 0 ≤ m := (norm_nonneg _).trans ha
  have hmul : ‖a‖*‖y‖ ≤ m :=
    (mul_le_of_le_one_right (norm_nonneg _) hy.le).trans ha
  have hden : 1-m ≤ ‖1-conj a*y‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (conj a*y)
    simp only [norm_one,norm_mul,_root_.Complex.norm_conj] at hh
    linarith
  have hden2 : (1-m)^2 ≤ ‖1-conj a*y‖^2 :=
    pow_le_pow_left₀ (by linarith) hden 2
  have hmt2 : ‖mobius a y‖^2 ≤ t := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hmt 2
    nlinarith
  have hn : 0 ≤ 1-‖mobius a y‖^2 := by nlinarith
  calc
    _ ≤ ‖1-conj a*y‖^2*(1-‖mobius a y‖^2) :=
      mul_le_mul hden2 (by linarith) (by linarith) (sq_nonneg _)
    _ = (1-‖a‖^2)*(1-‖y‖^2) :=
      (mul_comm _ _).trans (mobius_deficit_identity ha' hy)
    _ ≤ 1-‖y‖^2 := mul_le_of_le_one_left
      (by nlinarith [norm_nonneg y]) (by nlinarith [sq_nonneg ‖a‖])
    _ ≤ 2*(1-‖y‖) := by nlinarith [sq_nonneg (1-‖y‖)]



theorem disk_distance_from_interior_ball {f : ℂ → ℂ} {c x : ℂ} {r m : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r))
    (hf : MapsTo f (ball c r) (ball 0 1)) (hx : x ∈ ball c r)
    (hm : m < 1) (hfc : ‖f c‖ ≤ m) :
    (1-m)^2*(r-dist x c) ≤ 2*r*(1-‖f x‖) := by
  have hr : 0 < r := nonempty_ball.mp ⟨x,hx⟩
  have ht : dist x c/r < 1 := (div_lt_one hr).mpr hx
  have H := mobius_boundary_deficit hm hfc (mem_ball_zero_iff.mp (hf hx)) ht
    (schwarz_mobius_ball hd hf hx)
  have H' := mul_le_mul_of_nonneg_left H hr.le
  have hcancel : r*((1-m)^2*(1-dist x c/r)) = (1-m)^2*(r-dist x c) := by
    field_simp
  rw [hcancel] at H'
  nlinarith only [H']

end StrictHotSpots.Riemann
end
end RiemannSchwarz


end OAI
