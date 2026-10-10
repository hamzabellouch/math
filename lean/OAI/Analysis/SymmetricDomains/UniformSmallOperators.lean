import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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
namespace Release061

section

lemma continuousOn_uniformly_compact {P E F : Type*} [TopologicalSpace P]
    [TopologicalSpace E] [PseudoMetricSpace F]
    {K : Set E} (hK : IsCompact K) {V : Set P} {p₀ : P} (hV : V ∈ 𝓝 p₀)
    {f : P → E → F} (hf : ContinuousOn (Function.uncurry f) (V ×ˢ K)) :
    TendstoUniformlyOn f (f p₀) (𝓝 p₀) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨W,hW,hw⟩ := hK.mem_uniformity_of_prod hf (mem_of_mem_nhds hV)
    (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_eq_nhds.mpr hV] at hW
  filter_upwards [hW] with p hp
  intro x hx
  simpa only [Set.mem_ofPred_eq,dist_comm] using hw p hp x hx

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma c1_partial_family {f : P × E → F} {S : Set (P × E)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ 1 f S) :
    ContinuousOn (fun q : P × E => fderiv ℝ (fun x => f (q.1,x)) q.2) S := by
  have hfull : ContinuousOn (fderiv ℝ f) S := by
    intro q hq
    exact ((hf q hq).contDiffAt (hS.mem_nhds hq)).continuousAt_fderiv (by norm_num) |>.continuousWithinAt
  have heq : ∀ q ∈ S, fderiv ℝ (fun x => f (q.1,x)) q.2 =
      (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ P E) := by
    intro q hq
    have hd := ((hf q hq).contDiffAt (hS.mem_nhds hq)).differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp q.2 ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))).fderiv
  apply ContinuousOn.congr _ heq
  exact hfull.clm_comp continuousOn_const

theorem c1_family_uniformly_compact {f : P × E → F} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {K : Set E} (hK : IsCompact K) {p₀ : P}
    (hKS : {p₀} ×ˢ K ⊆ S) :
    TendstoUniformlyOn (fun p x => f (p,x)) (fun x => f (p₀,x)) (𝓝 p₀) K ∧
      TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => f (p,y)) x)
        (fun x => fderiv ℝ (fun y => f (p₀,y)) x) (𝓝 p₀) K := by
  obtain ⟨V,W,hV,_,hpV,hKW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton hK hS hKS
  have hp : V ∈ 𝓝 p₀ := hV.mem_nhds (hpV (mem_singleton p₀))
  have hsub : V ×ˢ K ⊆ S := fun q hq => hVW ⟨hq.1,hKW hq.2⟩
  exact ⟨continuousOn_uniformly_compact hK hp (hf.continuousOn.mono hsub),
    continuousOn_uniformly_compact hK hp ((c1_partial_family hS hf).mono hsub)⟩

end

variable {ι E F G : Type*} [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

lemma uniformly_eventually_norm_bounded {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContinuousOn f K) {v : ι → E → F} {l : Filter ι}
    (hv : TendstoUniformlyOn v f l K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in l, ∀ x ∈ K, ‖v t x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  refine ⟨1+max 0 C,by positivity,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hv) 1 (by norm_num)] with t ht
  intro x hx
  have hdist : ‖v t x-f x‖ < 1 := by
    simpa only [dist_eq_norm,norm_sub_rev] using ht x hx
  calc
    ‖v t x‖ = ‖(v t x-f x)+f x‖ := by rw [sub_add_cancel]
    _ ≤ ‖v t x-f x‖+‖f x‖ := norm_add_le _ _
    _ ≤ 1+max 0 C := add_le_add hdist.le ((hC _ (mem_image_of_mem f hx)).trans (le_max_right _ _))

omit [TopologicalSpace E] in
lemma uniform_zero_of_norm_bound {K : Set E} {v : ι → E → F} {l : Filter ι}
    {a : ι → ℝ} (ha : Tendsto a l (𝓝 0)) {C : ℝ}
    (hb : ∀ᶠ t in l, ∀ x ∈ K, ‖v t x‖ ≤ a t*C) :
    TendstoUniformlyOn v (fun _ => 0) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : ∀ᶠ t in l, a t*C < ε := by
    exact (tendsto_order.mp (by simpa using ha.mul_const C)).2 ε hε
  filter_upwards [hb,he] with t ht he
  intro x hx
  simpa only [dist_zero_left] using lt_of_le_of_lt (ht x hx) he

lemma uniform_small_operators [NormedSpace ℝ F] [NormedSpace ℝ G]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : ContinuousOn f K)
    {v : ι → E → F} {l : Filter ι} (hv : TendstoUniformlyOn v f l K)
    (L : ι → F →L[ℝ] G) (hL : Tendsto (fun t => ‖L t‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun t x => L t (v t x)) (fun _ => 0) l K := by
  obtain ⟨C,_,hC⟩ := uniformly_eventually_norm_bounded hK hf hv
  apply uniform_zero_of_norm_bound hL (C := C)
  filter_upwards [hC] with t ht
  intro x hx
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht x hx) (norm_nonneg _))

end Release061

end

end OAI
