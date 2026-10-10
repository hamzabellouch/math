import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.SplitTrial
import OAI.Analysis.BiholderTransport.LinearAlgebra.SchurRatioTendstoBot

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma split_regular_legs_eventually {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∀ᶠ w in 𝓝 p, t • w ∈ injectivityDomain x ∧
      (1-t) • (sprayFlow t (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hL : ∀ᶠ w in 𝓝 p, t • w ∈ injectivityDomain x :=
    (show ContinuousAt (fun w : V => t • w) p from by fun_prop).preimage_mem_nhds
      ((isOpen_injectivityDomain x).mem_nhds hleft)
  let Z : V → TangentBundle 𝓘(ℝ,Model n) M :=
    fun w => tangentScale (1-t) (sprayFlow t ⟨x,w⟩)
  have hZ : ContMDiff 𝓘(ℝ,V) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp (contMDiff_const.prodMk (contMDiff_spray_fiber x t))
  have hR : ∀ᶠ w in 𝓝 p, Z w ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} :=
    hZ.continuous.continuousAt.preimage_mem_nhds (isOpen_total_injectivityDomain.mem_nhds hright)
  exact hL.and hR

lemma conjugate_radial_hessian_tendsto_atBot {x : M} {p xi k : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0)
    (hpair : inner ℝ k xi≠0) :
    Tendsto (fun r : ℝ => hessianValue x (r • p) xi) (𝓝[<] 1) atBot := by
  obtain ⟨t,ht,ht1,hleft,hright⟩ := exists_minimizing_two_regular_legs hp
  have hline : Tendsto (fun r : ℝ => r • p) (𝓝[<] 1) (𝓝 p) := by
    simpa only [one_smul] using
      (show ContinuousAt (fun r : ℝ => r • p) 1 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have ha := ((splitTrialValue_contDiffAt hleft hright xi 0).continuousAt.tendsto).comp hline
  have hQ := ((splitTrialValue_contDiffAt hleft hright 0 k).continuousAt.tendsto).comp hline
  rw [splitTrialValue_conjugate_null ht ht1 hleft hright hk] at hQ
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] 1,
      0<splitTrialValue x t 0 k (r • p) ∧ hessianValue x (r • p) xi ≤
        splitTrialValue x t xi 0 (r • p)-(inner ℝ k xi)^2/splitTrialValue x t 0 k (r • p) := by
    filter_upwards [hline.eventually (split_regular_legs_eventually hleft hright),
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hr0 hr1
    exact splitTrialValue_schur ht ht1 (contracted_minimizer_mem_injectivityDomain hp hr0 hr1)
      hr.1 hr.2 hpair
  exact schur_ratio_tendsto_atBot ha hQ (sq_pos_of_ne_zero hpair) (hnear.mono (fun _ h => h.1))
    (hnear.mono (fun _ h => h.2))
end WeakMTWTransport

end

end OAI
