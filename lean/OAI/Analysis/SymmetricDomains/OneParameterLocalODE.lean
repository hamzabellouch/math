import Mathlib
import OAI.Analysis.SymmetricDomains.LocalAutomorphismODEGroup2
import OAI.Analysis.SymmetricDomains.NormalizedAutomorphismLimitComplete

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

theorem normalized_automorphism_sequence_complete (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (h : ℕ → ℝ) (hp : ∀ i, 0<h i)
    (hh : Tendsto h atTop (𝓝 0)) (p : U) (X : Affine n → Affine n)
    (hq : TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)) X atTop U) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ EqOn (infinitesimalGenerator H) X U := by
  have hdiff : DifferentiableOn ℂ X U := differentiableOn_of_locally_uniform_limit hU hq (by
    intro x hx
    refine ⟨U,hU.mem_nhds hx,Eventually.of_forall ?_⟩
    intro i y hy
    exact ((((q i).ambientAut_analytic hU y hy).differentiableAt.sub
      differentiableAt_id).const_smul (h i)⁻¹).differentiableWithinAt)
  have hX : AnalyticOnNhd ℂ X U := analyticOnNhd_of_differentiableOn_affine hU hdiff
  exact normalized_automorphism_limit_complete hU hc hbd Γ hhol atTop q h hp hh p X hX hq

theorem normalized_automorphism_sequence_isCompleteGenerator (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (h : ℕ → ℝ) (hp : ∀ i, 0<h i)
    (hh : Tendsto h atTop (𝓝 0)) (p : U) (X : Affine n → Affine n)
    (hq : TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)) X atTop U) :
    IsCompleteGenerator U (U.indicator X) := by
  classical
  obtain ⟨H,hH0,hHc,hHm,hHX⟩ := normalized_automorphism_sequence_complete hU hc hbd Γ hhol q h hp hh p X hq
  refine ⟨H,hHc,hH0,hHm,?_⟩
  funext x
  by_cases hx : x∈U
  · simpa only [indicator_of_mem hx] using hHX hx
  · simp only [indicator_of_notMem hx,infinitesimalGenerator_of_not_mem H hx]

theorem exists_oneParameter_of_local_ODE_germ (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (p : U) (X : Affine n → Affine n)
    (hX : ContDiffAt ℝ 1 X p.val)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ infinitesimalGenerator H=ᶠ[𝓝 p.val] X := by
  obtain ⟨ε,hε,_,hm⟩ := local_automorphism_ODE_group_law_of_contDiffAt hU hc p X hX g hg0 hr hδ hball hgc hd
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  obtain ⟨H,hH0,hHc,hHm,hHloc⟩ := local_real_hom_extension g hg0 hgc0 hε hm
  refine ⟨H,hH0,hHc,hHm,?_⟩
  filter_upwards [closedBall_mem_nhds p.val hr] with x hx
  have hdx := hd x hx 0 ⟨by linarith,hδ⟩
  have heq : (fun t => (g t).ambientAut x)=ᶠ[𝓝 (0:ℝ)] (fun t => (H t).ambientAut x) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht
    rw [hHloc t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)]
  have hdH := hdx.congr_of_eventuallyEq heq
  have heq0 : (g 0).ambientAut x=x := by rw [hg0,ambientAut_apply 1 ⟨x,hball hx⟩,one_apply]
  change deriv (fun t => (H t).ambientAut x) 0=X x
  simpa only [heq0] using hdH.hasDerivAt.deriv
end Biholomorph
end Release061

end

end OAI
