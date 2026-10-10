import Mathlib
import OAI.Analysis.SymmetricDomains.ScalingExpanding
import OAI.Analysis.SymmetricDomains.Pair

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

theorem bounded_divisible_automorphisms_subsequence {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (b : ℕ → Biholomorph U U) (p : U)
    (hanchor : ∃ K : Set U, IsCompact K ∧ ∀ᶠ j in atTop, (b j).toHomeomorph p ∈ K) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ e : Biholomorph U U,
      TendstoLocallyUniformlyOn
        (fun j => ambientExtend (fun x : U => ((b (ρ j)).toHomeomorph x).val))
        (ambientExtend (fun x : U => (e.toHomeomorph x).val)) atTop U ∧
      TendstoLocallyUniformlyOn
        (fun j => ambientExtend (fun x : U => ((b (ρ j)).toHomeomorph.symm x).val))
        (ambientExtend (fun x : U => (e.toHomeomorph.symm x).val)) atTop U := by
  let f : ℕ → Affine n → Affine n := fun j =>
    ambientExtend (fun x : U => ((b j).toHomeomorph x).val)
  let g : ℕ → Affine n → Affine n := fun j =>
    ambientExtend (fun x : U => ((b j).toHomeomorph.symm x).val)
  have hfval (j : ℕ) (x : U) : f j x.val=((b j).toHomeomorph x).val := ambientExtend_apply _ x
  have hgval (j : ℕ) (x : U) : g j x.val=((b j).toHomeomorph.symm x).val := ambientExtend_apply _ x
  have hfa : ∀ j, AnalyticOnNhd ℂ (f j) U := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open hU
    simpa only [hfval j] using (b j).holomorphic_toFun
  have hga : ∀ j, AnalyticOnNhd ℂ (g j) U := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open hU
    simpa only [hgval j] using (b j).holomorphic_invFun
  have hfm : ∀ j, MapsTo (f j) U U := fun j x hx => by
    rw [hfval j ⟨x,hx⟩]; exact ((b j).toHomeomorph ⟨x,hx⟩).property
  have hgm : ∀ j, MapsTo (g j) U U := fun j x hx => by
    rw [hgval j ⟨x,hx⟩]; exact ((b j).toHomeomorph.symm ⟨x,hx⟩).property
  have hgf : ∀ j x, x ∈ U → g j (f j x)=x := by
    intro j x hx
    rw [hfval j ⟨x,hx⟩,hgval j ((b j).toHomeomorph ⟨x,hx⟩)]
    exact congrArg Subtype.val ((b j).toHomeomorph.symm_apply_apply ⟨x,hx⟩)
  have hfg : ∀ j x, x ∈ U → f j (g j x)=x := by
    intro j x hx
    rw [hgval j ⟨x,hx⟩,hfval j ((b j).toHomeomorph.symm ⟨x,hx⟩)]
    exact congrArg Subtype.val ((b j).toHomeomorph.apply_symm_apply ⟨x,hx⟩)
  obtain ⟨R,hR,hRU⟩ := hb.exists_pos_norm_le
  obtain ⟨P,hPa,ρ,hρ,hP⟩ := montel_expanding_domains hU
      (fun j x => (f j x,g j x)) (by
    intro x hx
    obtain ⟨r,hr,hrU⟩ := isOpen_iff.mp hU x hx
    refine ⟨r,hr,R,hR,hrU,Eventually.of_forall fun j => ?_⟩
    refine ⟨((hfa j).differentiableOn.mono hrU).prodMk ((hga j).differentiableOn.mono hrU),?_⟩
    intro y hy
    exact norm_prod_le_iff.mpr ⟨hRU _ (hfm j (hrU hy)),hRU _ (hgm j (hrU hy))⟩)
  let F : Affine n → Affine n := fun x => (P x).1
  let G : Affine n → Affine n := fun x => (P x).2
  have hFa : AnalyticOnNhd ℂ F U := analyticOnNhd_of_differentiableOn_affine hU hPa.fst
  have hGa : AnalyticOnNhd ℂ G U := analyticOnNhd_of_differentiableOn_affine hU hPa.snd
  have hF : TendstoLocallyUniformlyOn (fun j => f (ρ j)) F atTop U :=
    locallyUniform_postcomp hP hPa.continuousOn continuous_fst
  have hG : TendstoLocallyUniformlyOn (fun j => g (ρ j)) G atTop U :=
    locallyUniform_postcomp hP hPa.continuousOn continuous_snd
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  have hFM : MapsTo F U U := by
    have he := bounded_cocompact_holomorphic_family_limit U hU hc U hb hhol K hK hrep
      (fun j => (b (ρ j)).toHomeomorph) atTop p
      (by obtain ⟨A,hA,ha⟩ := hanchor; exact ⟨A,hA,hρ.tendsto_atTop.eventually ha⟩)
      (HolomorphicOnSubset.locallyEventually hU (fun j => (b (ρ j)).holomorphic_toFun) atTop)
      (fun x => F x.val) (fun x => by simpa only [hfval] using hF.tendsto_at x.property)
    exact fun x hx => he ⟨x,hx⟩
  have hGp : G (F p.val)=p.val := by
    have ht : Tendsto (fun j => f (ρ j) p.val) atTop (𝓝[U] F p.val) :=
      tendsto_nhdsWithin_iff.mpr ⟨hF.tendsto_at p.property,Eventually.of_forall fun j => hfm (ρ j) p.property⟩
    exact tendsto_nhds_unique
      (hG.tendsto_comp (hGa.continuousOn _ (hFM p.property)) (hFM p.property) ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hgf (ρ j) p.val p.property).symm))
  have hGanchor : ∃ A : Set U, IsCompact A ∧ ∀ᶠ j in atTop,
      (b (ρ j)).toHomeomorph.symm ⟨F p.val,hFM p.property⟩ ∈ A := by
    obtain ⟨r,hr,hrU⟩ := isOpen_iff.mp hU p.val p.property
    let A : Set U := Subtype.val ⁻¹' closedBall p.val (r/2)
    have hclosedU : closedBall p.val (r/2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hrU
    have himage : Subtype.val '' A=closedBall p.val (r/2) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy
      · intro hx; exact ⟨⟨x,hclosedU hx⟩,hx,rfl⟩
    refine ⟨A,?_,?_⟩
    · apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [himage]
      exact isCompact_closedBall _ _
    · have ht : Tendsto (fun j => g (ρ j) (F p.val)) atTop (𝓝 p.val) := by
        simpa only [hGp] using hG.tendsto_at (hFM p.property)
      filter_upwards [ht.eventually (closedBall_mem_nhds p.val (half_pos hr))] with j hj
      change ((b (ρ j)).toHomeomorph.symm ⟨F p.val,hFM p.property⟩).val ∈ closedBall p.val (r/2)
      rw [← hgval (ρ j) ⟨F p.val,hFM p.property⟩]
      exact hj
  have hGM : MapsTo G U U := by
    have he := bounded_cocompact_holomorphic_family_limit U hU hc U hb hhol K hK hrep
      (fun j => (b (ρ j)).toHomeomorph.symm) atTop ⟨F p.val,hFM p.property⟩ hGanchor
      (HolomorphicOnSubset.locallyEventually hU (fun j => (b (ρ j)).holomorphic_invFun) atTop)
      (fun x => G x.val) (fun x => by simpa only [hgval] using hG.tendsto_at x.property)
    exact fun x hx => he ⟨x,hx⟩
  have hGF : ∀ x ∈ U, G (F x)=x := by
    intro x hx
    have ht : Tendsto (fun j => f (ρ j) x) atTop (𝓝[U] F x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hF.tendsto_at hx,Eventually.of_forall fun j => hfm (ρ j) hx⟩
    exact tendsto_nhds_unique
      (hG.tendsto_comp (hGa.continuousOn _ (hFM hx)) (hFM hx) ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hgf (ρ j) x hx).symm))
  have hFG : ∀ x ∈ U, F (G x)=x := by
    intro x hx
    have ht : Tendsto (fun j => g (ρ j) x) atTop (𝓝[U] G x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hG.tendsto_at hx,Eventually.of_forall fun j => hgm (ρ j) hx⟩
    exact tendsto_nhds_unique
      (hF.tendsto_comp (hFa.continuousOn _ (hGM hx)) (hGM hx) ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hfg (ρ j) x hx).symm))
  let e := biholomorphOfAmbientInverse U U F G hFa hGa hFM hGM hGF hFG
  refine ⟨ρ,hρ,e,?_,?_⟩
  · apply hF.congr_right
    intro x hx
    change F x = ambientExtend (fun x : U => F x.val) x
    exact (ambientExtend_apply (fun x : U => F x.val) ⟨x,hx⟩).symm
  · apply hG.congr_right
    intro x hx
    change G x = ambientExtend (fun x : U => G x.val) x
    exact (ambientExtend_apply (fun x : U => G x.val) ⟨x,hx⟩).symm

end Release061

end

end OAI
