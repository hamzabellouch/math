import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiniteActiveGrowth
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.Geodesics.BranchExtension

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

lemma cost_branch_normal_jets {x : M} {r : TangentSpace 𝓘(ℝ,Model n) x}
    {T : ℝ} (hT : 0 < T) {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • r)))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, t • r ∈ injectivityDomain x) :
    let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      G (riemannianExp x h,riemannianExp x (T • r))
    ContDiffAt ℝ ∞ f 0 ∧ HasFDerivAt f (innerSL ℝ (-(T • r))) 0 ∧
      ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x,
      Tendsto (fun t : ℝ => hessianValue x (t • r) ξ) (𝓝[<] T)
        (𝓝 (fderiv ℝ (fderiv ℝ f) 0 ξ ξ)) := by
  let F := fun (t : ℝ) (h : TangentSpace 𝓘(ℝ,Model n) x) =>
    G (riemannianExp x h,riemannianExp x (t • r))
  have hfamily : ContDiffAt ℝ ∞ (Function.uncurry F) (T,0) := smooth_branch_normal_family hG
  have hFT : ContDiffAt ℝ ∞ (F T) 0 := hfamily.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have H : ∀ᶠ t in 𝓝[<] T, t • r ∈ injectivityDomain x ∧
      normalCost x (t • r) =ᶠ[𝓝 0] F t := by
    filter_upwards [(cost_branch_normal_eventuallyEq hagree).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht ht0 htT
    have htID := hID t ⟨ht0,htT⟩
    exact ⟨htID,ht htID⟩
  have hL : ContinuousAt (fun t => fderiv ℝ (F t) 0) T :=
    (ContDiffAt.partial_snd_fderiv hfamily).continuousAt.comp (f := fun t : ℝ => (t,(0 : TangentSpace 𝓘(ℝ,Model n) x)))
      (continuousAt_id.prodMk continuousAt_const)
  have hLe : fderiv ℝ (F T) 0 = innerSL ℝ (-(T • r)) := by
    have hR : ContinuousAt (fun t : ℝ => innerSL ℝ (-(t • r))) T := by fun_prop
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[<] T)
      (hL.tendsto.mono_left nhdsWithin_le_nhds) (hR.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [H] with t ht
    rw [←ht.2.fderiv_eq]
    exact (normalCost_hasFDerivAt_zero ht.1).fderiv
  refine ⟨hFT,?_,?_⟩
  · rw [←hLe]
    exact (hFT.differentiableAt (by simp)).hasFDerivAt
  · intro ξ
    have hB : ContinuousAt (fun t => fderiv ℝ (fderiv ℝ (F t)) 0 ξ ξ) T :=
      (((ContDiffAt.partial_snd_fderiv_two hfamily).continuousAt.comp (f := fun t : ℝ => (t,(0 : TangentSpace 𝓘(ℝ,Model n) x)))
        (continuousAt_id.prodMk continuousAt_const)).clm_apply continuousAt_const).clm_apply continuousAt_const
    apply (hB.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [H] with t ht
    rw [hessianValue_eq_normalHessian ht.1]
    dsimp only [normalHessian]
    rw [ht.2.fderiv.fderiv_eq]

end WeakMTWTransport

end

end OAI
