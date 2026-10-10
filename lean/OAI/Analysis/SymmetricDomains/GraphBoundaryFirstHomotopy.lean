import Mathlib

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
namespace Release061

section
variable {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]

lemma compact_image_perturbation {K : Set P} (hK : IsCompact K)
    {G : P → E} (hG : ContinuousOn G K) {Ω : Set E} (hΩ : IsOpen Ω)
    (himage : G '' K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K, ∀ v : E, ‖v‖ < ε → G p+v ∈ Ω := by
  obtain ⟨ε,hε,hsub⟩ := (hK.image_of_continuousOn hG).exists_thickening_subset_open hΩ himage
  refine ⟨ε,hε,?_⟩
  intro p hp v hv
  apply hsub
  apply mem_thickening_iff.mpr
  exact ⟨G p,mem_image_of_mem G hp,by simpa only [dist_eq_norm,add_sub_cancel_left] using hv⟩

end

open Set Metric
variable {E F Θ : Type*} [NormedAddCommGroup E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem graph_boundary_perturbation
    {Ω : Set F} (hΩ : IsOpen Ω) {G : E × ℝ → F}
    {r u₀ α d L M : ℝ} (hα : 0 < α)
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hu : α*L+d < u₀)
    (hG : ContinuousOn G (closedBall 0 r ×ˢ Icc α (α+d)))
    (hgraph : ∀ x ∈ closedBall 0 r, ∀ u ∈ Ioo 0 u₀, G (x,u) ∈ Ω)
    {lam eta : Θ → ℝ} (hlam : ∀ θ, 0 ≤ lam θ ∧ lam θ ≤ L)
    (heta : ∀ θ, |eta θ| ≤ M)
    (hsupport : ∀ θ, eta θ ≠ 0 → lam θ = 1) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ x ∈ closedBall 0 r, ∀ θ, ∀ δ ∈ Ioc 0 d,
      ∀ e : F, ‖e‖ < e₀ → G (x,α*lam θ+δ)+eta θ • e ∈ Ω := by
  have hαL : α ≤ α*L := by nlinarith
  have himage : G '' (closedBall 0 r ×ˢ Icc α (α+d)) ⊆ Ω := by
    rintro _ ⟨⟨x,u⟩,⟨hx,hu'⟩,rfl⟩
    exact hgraph x hx u ⟨lt_of_lt_of_le hα hu'.1,by linarith [hu'.2]⟩
  obtain ⟨ε,hε,hpert⟩ := compact_image_perturbation
    ((isCompact_closedBall (0 : E) r).prod isCompact_Icc) hG hΩ himage
  refine ⟨ε/(M+1),div_pos hε (by positivity),?_⟩
  intro x hx θ δ hδ e he
  by_cases hη : eta θ = 0
  · rw [hη,zero_smul,add_zero]
    exact hgraph x hx _ ⟨by nlinarith [(hlam θ).1,hδ.1],by nlinarith [(hlam θ).2,hδ.2]⟩
  · rw [hsupport θ hη,mul_one]
    apply hpert (x,α+δ) ⟨hx,⟨by linarith [hδ.1],by linarith [hδ.2]⟩⟩
    rw [norm_smul,Real.norm_eq_abs]
    have hsmall : (M+1)*‖e‖ < ε := by
      have := (lt_div_iff₀ (by positivity : 0 < M+1)).mp he
      nlinarith
    calc |eta θ| * ‖e‖ ≤ M*‖e‖ := mul_le_mul_of_nonneg_right (heta θ) (norm_nonneg _)
      _ ≤ (M+1)*‖e‖ := by nlinarith [norm_nonneg e]
      _ < ε := hsmall

omit [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] in

lemma graph_boundary_first_homotopy
    {Ω : Set F} {G : E × ℝ → F} {r u₀ α d L : ℝ}
    (hα : 0 ≤ α) (hu : α*L+d < u₀)
    (hgraph : ∀ x ∈ closedBall 0 r, ∀ u ∈ Ioo 0 u₀, G (x,u) ∈ Ω)
    {lam : Θ → ℝ} (hlam : ∀ θ, 0 ≤ lam θ ∧ lam θ ≤ L)
    {x : E} (hx : x ∈ closedBall 0 r) (θ : Θ)
    {s δ : ℝ} (hs : s ∈ Icc 0 α) (hδ : δ ∈ Ioc 0 d) :
    G (x,s*lam θ+δ) ∈ Ω := by
  apply hgraph x hx
  refine ⟨by nlinarith [(hlam θ).1,hs.1,hδ.1],?_⟩
  have hmul := mul_le_mul hs.2 (hlam θ).2 (hlam θ).1 hα
  linarith [hδ.2]

end Release061

end

end OAI
