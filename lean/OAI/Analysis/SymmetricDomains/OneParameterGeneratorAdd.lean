import Mathlib
import OAI.Analysis.SymmetricDomains.LocalAutomorphismODEGroup
import OAI.Analysis.SymmetricDomains.LocalRealHomExtension

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

theorem exists_oneParameter_of_local_ODE (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U) (p : U)
    (X : Affine n → Affine n) (hX : AnalyticOnNhd ℂ X U)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ EqOn (infinitesimalGenerator H) X U := by
  obtain ⟨ε,hε,_,hm⟩ := local_automorphism_ODE_group_law hU hc p X hX g hg0 hr hδ hball hgc hd
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  obtain ⟨H,hH0,hHc,hHm,hHloc⟩ := local_real_hom_extension g hg0 hgc0 hε hm
  refine ⟨H,hH0,hHc,hHm,?_⟩
  apply (infinitesimalGenerator_analytic hU H hHc hbd hH0 hHm).eqOn_of_preconnected_of_eventuallyEq
    hX hc p.property
  filter_upwards [closedBall_mem_nhds p.val hr] with x hx
  have hdx := hd x hx 0 ⟨by linarith,hδ⟩
  have heq : (fun t => (g t).ambientAut x)=ᶠ[𝓝 (0:ℝ)] (fun t => (H t).ambientAut x) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht
    rw [hHloc t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)]
  have hdH := hdx.congr_of_eventuallyEq heq
  have heq0 : (g 0).ambientAut x=x := by rw [hg0,ambientAut_apply 1 ⟨x,hball hx⟩,one_apply]
  change deriv (fun t => (H t).ambientAut x) 0=X x
  simpa only [heq0] using hdH.hasDerivAt.deriv

theorem exists_oneParameter_generator_add (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ ∀ x∈U,
        infinitesimalGenerator H x=infinitesimalGenerator a x+infinitesimalGenerator b x := by
  obtain ⟨p,hp⟩ := hc.nonempty
  obtain ⟨r,hr,δ,hδ,g,hball,hg0,hgc,_,hgd⟩ := productCurve_local_automorphism_family
    hU hc.isPreconnected hbd Γ hhol a b ha hb ha0 ham hb0 hbm ⟨p,hp⟩
  exact exists_oneParameter_of_local_ODE hU hc.isPreconnected hbd ⟨p,hp⟩
    (fun x => infinitesimalGenerator a x+infinitesimalGenerator b x)
    (fun x hx => (infinitesimalGenerator_analytic hU a ha hbd ha0 ham x hx).add
      (infinitesimalGenerator_analytic hU b hb hbd hb0 hbm x hx)) g hg0 hr hδ hball hgc hgd

end Biholomorph
end Release061

end

end OAI
