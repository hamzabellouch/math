import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions
import OAI.Analysis.BiholderTransport.Coordinates.RadialIdentity

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_branch_agrees_on_minimizing
    {z : TangentBundle 𝓘(ℝ,Model n) M} {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (z.1,riemannianExp z.1 z.2))
    (hagree : ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
      (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G) :
    ∀ᶠ r in 𝓝 z, r.2 ∈ minimizingVectors r.1 →
      cost r.1 (riemannianExp r.1 r.2) = G (r.1,riemannianExp r.1 r.2) := by
  let F := fun r : TangentBundle 𝓘(ℝ,Model n) M => (r.1, riemannianExp r.1 r.2)
  have hF : Continuous F := (FiberBundle.continuous_proj _ _).prodMk contMDiff_riemannianExp.continuous
  have hGc : ∀ᶠ q in 𝓝 (F z), ContinuousAt G q := by
    have H := (contMDiffAt_iff_contMDiffAt_nhds
      (by norm_num : (1 : WithTop ℕ∞) ≠ (↑(⊤:ℕ∞) : WithTop ℕ∞))).mp
        (hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    exact H.mono (fun q hq => hq.continuousAt)
  filter_upwards [eventually_eventually_nhds.mpr hagree,hF.continuousAt.eventually hGc] with r hr hc hmin
  have hrcl : r.2 ∈ closure (injectivityDomain r.1) := by rwa [closure_injectivityDomain]
  have : NeBot (𝓝[injectivityDomain r.1] r.2) := mem_closure_iff_nhdsWithin_neBot.mp hrcl
  have hi : Continuous (fun p : TangentSpace 𝓘(ℝ,Model n) r.1 =>
      (⟨r.1,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    FiberBundle.continuous_totalSpaceMk (Model n) _ r.1
  have heq : (fun p => cost r.1 (riemannianExp r.1 p)) =ᶠ[𝓝[injectivityDomain r.1] r.2]
      (fun p => G (r.1,riemannianExp r.1 p)) := by
    filter_upwards [(hi.continuousAt.eventually hr).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with p hp hpID
    exact (hp hpID).self_of_nhds
  have he : Continuous (fun p : TangentSpace 𝓘(ℝ,Model n) r.1 => (r.1,riemannianExp r.1 p)) :=
    continuous_const.prodMk (contMDiff_riemannianExp_fiber (n := n) r.1).continuous
  change ContinuousAt G (r.1,riemannianExp r.1 r.2) at hc
  have hg : ContinuousAt (fun p : TangentSpace 𝓘(ℝ,Model n) r.1 =>
      G (r.1,riemannianExp r.1 p)) r.2 := hc.comp (f := fun p : TangentSpace 𝓘(ℝ,Model n) r.1 =>
        (r.1,riemannianExp r.1 p)) (he.continuousAt (x := r.2))
  apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[injectivityDomain r.1] r.2)
    (((continuous_cost_right r.1).comp
      (contMDiff_riemannianExp_fiber (n := n) r.1).continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) heq

lemma smooth_branch_normal_family {x : M} {r : TangentSpace 𝓘(ℝ,Model n) x}
    {T : ℝ} {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • r))) :
    ContDiffAt ℝ ∞ (fun q : ℝ × TangentSpace 𝓘(ℝ,Model n) x =>
      G (riemannianExp x q.2,riemannianExp x (q.1 • r))) (T,0) := by
  have hG' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (riemannianExp (n := n) x 0,riemannianExp x (T • r)) := by simpa only [riemannianExp_zero] using hG
  have hL : ContMDiffAt 𝓘(ℝ,ℝ × TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ × TangentSpace 𝓘(ℝ,Model n) x => riemannianExp x q.2) (T,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (T,0) contDiffAt_snd.contMDiffAt
  have hR : ContMDiffAt 𝓘(ℝ,ℝ × TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ × TangentSpace 𝓘(ℝ,Model n) x => riemannianExp x (q.1 • r)) (T,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (T,0)
      (contDiffAt_fst.smul contDiffAt_const).contMDiffAt
  exact (hG'.comp (T,0) (hL.prodMk hR)).contDiffAt

lemma cost_branch_normal_eventuallyEq {x : M} {r : TangentSpace 𝓘(ℝ,Model n) x}
    {T : ℝ} {G : M × M → ℝ}
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∀ᶠ t in 𝓝 T, t • r ∈ injectivityDomain x →
      normalCost x (t • r) =ᶠ[𝓝 0] (fun h => G (riemannianExp x h,riemannianExp x (t • r))) := by
  have hi : Continuous (fun t : ℝ => (⟨x,t • r⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    (FiberBundle.continuous_totalSpaceMk (Model n) _ x).comp (continuous_id.smul continuous_const)
  filter_upwards [hi.continuousAt.eventually hagree] with t ht htID
  have hc : Tendsto (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      (riemannianExp x h,riemannianExp x (t • r))) (𝓝 0) (𝓝 (x,riemannianExp x (t • r))) := by
    have hcurve : ContinuousAt (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
        (riemannianExp x h,riemannianExp x (t • r))) 0 :=
      (contMDiff_riemannianExp_fiber x).continuous.continuousAt.prodMk continuousAt_const
    simpa only [riemannianExp_zero] using hcurve.tendsto
  exact (ht htID).comp_tendsto hc

end WeakMTWTransport

end

end OAI
