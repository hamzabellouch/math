import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedTaylorUniformlyCompact

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
namespace Release061
open Set Filter Metric
open scoped Topology

lemma compact_eventual_inclusion {X : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (D : ℝ → Set X)
    (htest : ∀ (t : ℕ → ℝ) (x : ℕ → X) (a : X),
      Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) → (∀ j, x j ∈ K) →
      a ∈ K → Tendsto x atTop (𝓝 a) → ∀ᶠ j in atTop, x j ∈ D (t j)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ D t := by
  by_contra h
  have hfreq : ∃ᶠ t : ℝ in 𝓝[>] 0, ¬ K ⊆ D t := not_eventually.mp h
  have hex (j : ℕ) : ∃ t : ℝ, 0 < t ∧ t < 1/((j:ℝ)+1) ∧ ∃ x ∈ K, x ∉ D t := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1/((j:ℝ)+1) :=
      (tendsto_order.mp (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0))).2 _ (by positivity)
    obtain ⟨t,ht,htp,hts⟩ := (hfreq.and_eventually ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and hsmall)).exists
    obtain ⟨x,hx,hxd⟩ := not_subset.mp ht
    exact ⟨t,htp,hts,x,hx,hxd⟩
  choose t htp hts x hx hxd using hex
  have ht : Tendsto t atTop (𝓝 0) := squeeze_zero (fun j => (htp j).le)
    (fun j => (hts j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a,ha,φ,hφ,hxa⟩ := hK.tendsto_subseq hx
  have hh := htest (t ∘ φ) (x ∘ φ) a (ht.comp hφ.tendsto_atTop)
    (fun j => htp (φ j)) (fun j => hx (φ j)) ha hxa
  obtain ⟨j,hj⟩ := hh.exists
  exact hxd (φ j) hj

lemma offsetDistance_pos_mem {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E)
    (h : 0 < offsetDistance A s t v) : v ∈ offsetScaled A s t := by
  by_contra hn
  have hz : offsetDistance A s t v = 0 := by
    rw [offsetDistance,infDist_zero_of_mem hn]
    norm_num
  exact (ne_of_gt h) hz

theorem compact_inclusion_from_offsets {X S E : Type*} [MetricSpace X]
    [PseudoMetricSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (D : ℝ → Set X) (s : ℝ → X → S) (Rₜ : ℝ → X → E)
    (R : X → E) (d : E → ℝ) (s₀ : S)
    {K : Set X} (hK : IsCompact K) (hRcont : ContinuousOn R K)
    (hs : TendstoUniformlyOn s (fun _ => s₀) (𝓝[>] (0 : ℝ)) K)
    (hR : TendstoUniformlyOn Rₜ R (𝓝[>] (0 : ℝ)) K)
    (hjoint : ∀ (s' : ℕ → S) (t' : ℕ → ℝ), Tendsto s' atTop (𝓝 s₀) →
      Tendsto t' atTop (𝓝 0) → (∀ j, 0 < t' j) → ∀ v : E,
      Tendsto (fun j => offsetDistance A (s' j) (t' j) v) atTop (𝓝 (d v)))
    (hmatch : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x ∈ K,
      (x ∈ D t ↔ Rₜ t x ∈ offsetScaled A (s t x) t))
    (hpos : ∀ x ∈ K, 0 < d (R x)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ D t := by
  apply compact_eventual_inclusion hK D
  intro t x a ht htp hx ha hxa
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htp⟩
  have hxa' : Tendsto x atTop (𝓝[K] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxa,Eventually.of_forall hx⟩
  have hs' : Tendsto (fun j => s (t j) (x j)) atTop (𝓝 s₀) :=
    (uniform_reindex hs ht').tendsto_comp continuousWithinAt_const hxa'
  have hR' : Tendsto (fun j => Rₜ (t j) (x j)) atTop (𝓝 (R a)) :=
    (uniform_reindex hR ht').tendsto_comp (hRcont a ha) hxa'
  have hd := moving_offsetDistance_limit A (fun j => s (t j) (x j)) t
    (hjoint _ t hs' ht htp (R a)) hR'
  filter_upwards [(tendsto_order.mp hd).1 0 (hpos a ha),ht'.eventually hmatch] with j hj hm
  exact (hm (x j) (hx j)).mpr (offsetDistance_pos_mem A _ _ _ hj)

lemma select_excluded_offsets {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : ℕ → S) (t : ℕ → ℝ) (v : ℕ → E)
    (hne : ∀ j, (offsetScaled A (s j) (t j))ᶜ.Nonempty)
    (hd : Tendsto (fun j => infDist (v j) (offsetScaled A (s j) (t j))ᶜ) atTop (𝓝 0)) :
    ∃ u : ℕ → E, (∀ j, u j ∉ offsetScaled A (s j) (t j)) ∧
      Tendsto (fun j => dist (u j) (v j)) atTop (𝓝 0) := by
  have hex (j : ℕ) : ∃ u ∈ (offsetScaled A (s j) (t j))ᶜ,
      dist (v j) u < infDist (v j) (offsetScaled A (s j) (t j))ᶜ+1/((j:ℝ)+1) :=
    (infDist_lt_iff (hne j)).mp (lt_add_of_pos_right _ (by positivity))
  choose u hu hdu using hex
  refine ⟨u,hu,?_⟩
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => by simpa only [dist_comm] using (hdu j).le)
  simpa only [zero_add] using hd.add tendsto_one_div_add_atTop_nhds_zero_nat

end Release061

end

end OAI
