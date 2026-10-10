import Mathlib
import OAI.Analysis.SymmetricDomains.NormalizedAutomorphismsHaveNonzero

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
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_displacement_maximum_normalization
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (q : ℕ → Biholomorph U U) (hq : Tendsto q atTop (𝓝 1)) (hne : ∀ i, q i≠1)
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U) :
    ∃ h : ℕ → ℝ, (∀ i, 0<h i) ∧ Tendsto h atTop (𝓝 0) ∧
      (∀ i, ∀ x∈closedBall p.val R, ‖(q i).ambientAut x-x‖≤h i) ∧
      (∀ i, ∃ x∈closedBall p.val R, h i≤‖(q i).ambientAut x-x‖) := by
  have hm (i : ℕ) : ∃ x∈closedBall p.val R,
      ∀ y∈closedBall p.val R, ‖(q i).ambientAut y-y‖≤‖(q i).ambientAut x-x‖ :=
    (isCompact_closedBall p.val R).exists_isMaxOn ⟨p.val,mem_closedBall_self hR.le⟩
      ((((q i).ambientAut_analytic hU).continuousOn.sub continuousOn_id).norm.mono hRU)
  choose x hxb hxm using hm
  let h : ℕ → ℝ := fun i => ‖(q i).ambientAut (x i)-x i‖
  have hp (i : ℕ) : 0<h i := by
    by_contra hn
    have hz : h i=0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    apply hne i
    apply eq_of_ambientAut_eventuallyEq hU hc p
    filter_upwards [closedBall_mem_nhds p.val hR] with y hy
    have hz' : ‖(q i).ambientAut (x i)-x i‖=0 := hz
    have hy0 : (q i).ambientAut y=y := sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [hz'] using hxm i y hy) (norm_nonneg _)))
    rw [hy0,ambientAut_apply 1 ⟨y,hRU hy⟩,one_apply]
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val R)).mp
    ((ambientAut_tendstoLocallyUniformly hq).mono hRU)
  have ht : Tendsto h atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with i hi
    have hb := hi (x i) (hxb i)
    rw [dist_eq_norm,sub_zero,Real.norm_eq_abs,abs_of_pos (hp i)]
    rw [ambientAut_apply 1 ⟨x i,hRU (hxb i)⟩,one_apply,dist_eq_norm,norm_sub_rev] at hb
    exact hb
  exact ⟨h,hp,ht,hxm,fun i => ⟨x i,hxb i,le_rfl⟩⟩

theorem small_automorphisms_have_nonzero_complete_tangent
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (hq : Tendsto q atTop (𝓝 1)) (hne : ∀ i, q i≠1)
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U) :
    ∃ h : ℕ → ℝ, (∀ i, 0<h i) ∧ Tendsto h atTop (𝓝 0) ∧
      ∃ X : Affine n → Affine n, IsCompleteGenerator U X ∧ X≠0 ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)) X atTop (ball p.val R) := by
  obtain ⟨h,hp,hh,hbound,hmax⟩ := exists_displacement_maximum_normalization hU hc q hq hne p hR hRU
  exact ⟨h,hp,hh,normalized_automorphisms_have_nonzero_complete_limit hU hc hbd Γ hhol q h hp hh p hR hRU hbound hmax⟩
end Biholomorph
end Release061

end

end OAI
