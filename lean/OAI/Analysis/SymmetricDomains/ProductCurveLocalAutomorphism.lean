import Mathlib
import OAI.Analysis.SymmetricDomains.ProductCurveLocalFlow

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
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_tendsto_of_compact_local_pointwise (hU : IsOpen U) (hc : IsPreconnected U)
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (K : Set (Biholomorph U U)) (hK : IsCompact K) (hq : ∀ᶠ i in l, q i∈K)
    (p : U) {r : ℝ} (hr : 0<r) (hballU : closedBall p.val r⊆U)
    (f : Affine n → Affine n)
    (hf : ∀ x∈closedBall p.val r, Tendsto (fun i => (q i).ambientAut x) l (𝓝 (f x))) :
    ∃ e : Biholomorph U U, Tendsto q l (𝓝 e) ∧ EqOn e.ambientAut f (closedBall p.val r) := by
  have hcluster (d : Biholomorph U U) (hd : MapClusterPt d l q) :
      EqOn d.ambientAut f (closedBall p.val r) := by
    intro x hx
    let xx : U := ⟨x,hballU hx⟩
    have hev : Continuous (fun d : Biholomorph U U => (d.toHomeomorph xx).val) :=
      continuous_subtype_val.comp (continuous_evaluation xx)
    have hd' := hd.continuousAt_comp hev.continuousAt
    have hf' : Tendsto (fun i => ((q i).toHomeomorph xx).val) l (𝓝 (f x)) := by
      have ht := hf x hx
      change Tendsto (fun i => (q i).ambientAut xx.val) l (𝓝 (f x)) at ht
      simpa only [ambientAut_apply] using ht
    have heq : (d.toHomeomorph xx).val=f x := eq_of_nhds_neBot (hd'.clusterPt.mono hf')
    change d.ambientAut xx.val=f x
    simpa only [ambientAut_apply] using heq
  obtain ⟨e,_,he⟩ := hK.exists_mapClusterPt (Filter.le_principal_iff.mpr hq)
  refine ⟨e,hK.tendsto_nhds_of_unique_mapClusterPt hq ?_,hcluster e he⟩
  intro d _ hd
  have hloc : d.ambientAut =ᶠ[𝓝 p.val] e.ambientAut := by
    filter_upwards [closedBall_mem_nhds p.val hr] with x hx
    exact (hcluster d hd hx).trans (hcluster e he hx).symm
  have hall := (d.ambientAut_analytic hU).eqOn_of_preconnected_of_eventuallyEq
    (e.ambientAut_analytic hU) hc p.property hloc
  apply ext
  intro x
  apply Subtype.ext
  simpa only [ambientAut_apply] using hall x.property

theorem eq_of_ambientAut_eventuallyEq (hU : IsOpen U) (hc : IsPreconnected U)
    (p : U) {a b : Biholomorph U U} (hab : a.ambientAut =ᶠ[𝓝 p.val] b.ambientAut) : a=b := by
  have hall := (a.ambientAut_analytic hU).eqOn_of_preconnected_of_eventuallyEq
    (b.ambientAut_analytic hU) hc p.property hab
  apply ext
  intro x
  apply Subtype.ext
  simpa only [ambientAut_apply] using hall x.property

theorem productCurve_local_automorphism_family (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∃ g : ℝ → Biholomorph U U,
      closedBall p.val r ⊆ U ∧ g 0=1 ∧ ContinuousOn g (Icc (-δ) δ) ∧
      (∀ t∈Icc (-δ) δ, Tendsto (fun N : ℕ => (a (t/(N+1))*b (t/(N+1)))^(N+1))
        atTop (𝓝 (g t))) ∧
      ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
        HasStrictDerivAt (fun s => (g s).ambientAut x)
          (infinitesimalGenerator a ((g t).ambientAut x)+
            infinitesimalGenerator b ((g t).ambientAut x)) t := by
  classical
  obtain ⟨r,hr,δ₀,hδ₀,α,hball,hα0,hα,hαc⟩ :=
    productCurve_local_flow_limit hU hbd a b ha hb ha0 ham hb0 hbm p
  obtain ⟨δ₁,hδ₁,K,hK,hpow⟩ := productCurve_powers_uniform_compact
    hU hc hbd Γ hhol a b ha hb ha0 ham hb0 hbm p
  let δ : ℝ := min δ₀ δ₁
  have hδ : 0<δ := lt_min hδ₀ hδ₁
  have hδ0 : δ≤δ₀ := min_le_left _ _
  have hδ1 : δ≤δ₁ := min_le_right _ _
  have ht0 {t : ℝ} (ht : t∈Icc (-δ) δ) : t∈Icc (-δ₀) δ₀ := by
    constructor <;> linarith [ht.1,ht.2]
  have hpK (t : ℝ) (ht : t∈Icc (-δ) δ) (N : ℕ) :
      (a (t/(N+1))*b (t/(N+1)))^(N+1)∈K :=
    hpow t ((abs_le.mpr ht).trans hδ1) N (N+1) le_rfl
  have hex (t : ℝ) : ∃ e : Biholomorph U U, t∈Icc (-δ) δ →
      Tendsto (fun N : ℕ => (a (t/(N+1))*b (t/(N+1)))^(N+1)) atTop (𝓝 e) ∧
      EqOn e.ambientAut (fun x => α x t) (closedBall p.val r) := by
    by_cases ht : t∈Icc (-δ) δ
    · obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc atTop
        (fun N : ℕ => (a (t/(N+1))*b (t/(N+1)))^(N+1)) K hK
        (Filter.Eventually.of_forall (hpK t ht)) p hr hball (fun x => α x t)
        (fun x hx => (hα x hx t (ht0 ht)).2.2)
      exact ⟨e,fun _ => ⟨he,heq⟩⟩
    · exact ⟨1,fun h => (ht h).elim⟩
  choose g hg using hex
  have hgK (t : ℝ) (ht : t∈Icc (-δ) δ) : g t∈K :=
    hK.isClosed.mem_of_tendsto (hg t ht).1 (Filter.Eventually.of_forall (hpK t ht))
  have hzero : (0:ℝ)∈Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hg0 : g 0=1 := by
    have ht := (hg 0 hzero).1
    have ht' : Tendsto (fun _ : ℕ => (1 : Biholomorph U U)) atTop (𝓝 (g 0)) := by
      simpa only [zero_div,ha0,hb0,one_mul,one_pow] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hgc : ContinuousOn g (Icc (-δ) δ) := by
    intro t ht
    have : NeBot (𝓝[Icc (-δ) δ] t) := nhdsWithin_neBot_of_mem ht
    have hv (x : Affine n) (hx : x∈closedBall p.val r) :
        Tendsto (fun s => (g s).ambientAut x) (𝓝[Icc (-δ) δ] t) (𝓝 (α x t)) := by
      have hpath : ContinuousOn (fun s => α x s) (Icc (-δ) δ) := hαc.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx,ht0 hs⟩)
      apply (hpath t ht).tendsto.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((hg s hs).2 hx).symm
    obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc
      (𝓝[Icc (-δ) δ] t) g K hK (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hgK s hs) p hr hball (fun x => α x t) hv
    have hegt : e=g t := eq_of_ambientAut_eventuallyEq hU hc p (by
      filter_upwards [closedBall_mem_nhds p.val hr] with x hx
      exact (heq hx).trans ((hg t ht).2 hx).symm)
    change Tendsto g (𝓝[Icc (-δ) δ] t) (𝓝 (g t))
    rw [hegt] at he
    exact he
  refine ⟨r,hr,δ,hδ,g,hball,hg0,hgc,(fun t ht => (hg t ht).1),?_⟩
  intro x hx t ht
  have htt : t∈Icc (-δ) δ := Ioo_subset_Icc_self ht
  have hed := (hα x hx t (ht0 htt)).2.1
  have heq : (fun s => α x s) =ᶠ[𝓝 t] (fun s => (g s).ambientAut x) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact ((hg s hs).2 hx).symm
  have htEq : (g t).ambientAut x=α x t := (hg t htt).2 hx
  rw [← htEq] at hed
  exact hed.congr_of_eventuallyEq heq

end Biholomorph
end Release061

end

end OAI
