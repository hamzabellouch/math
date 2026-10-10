import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.RelativeHessianBound
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MixedIntrinsic
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance finiteMixed (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] in
lemma chart_normal_smooth {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hp:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    ContDiffAt ℝ ∞ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp x) p := by
  apply ContMDiffAt.contDiffAt
  apply ContMDiffAt.comp p _ (contMDiff_riemannianExp_fiber x p)
  exact contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)

omit [Nonempty M] in
lemma mixed_intrinsic_factor {x a b:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp:p∈injectivityDomain x)
    (hy:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let T := fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp x) 0
    let S := fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp x) p
    T.adjoint.comp ((mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
      (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))).comp S)=
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,Model n) x) := by
  dsimp only
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let ψ:=extChartAt 𝓘(ℝ,Model n) b
  let f:=χ ∘ riemannianExp (n:=n) x
  let g:=ψ ∘ riemannianExp (n:=n) x
  let T:=fderiv ℝ f 0
  let S:=fderiv ℝ g p
  let G:=chartCostCovector (n:=n) a b
  have hf:ContDiffAt ℝ ∞ f 0:=chart_normal_smooth (by simpa only [riemannianExp_zero] using hx)
  have hg:ContDiffAt ℝ ∞ g p:=chart_normal_smooth hy
  have hf0:f 0=χ x:=by simp only [f,Function.comp_apply,riemannianExp_zero]
  have hgc:ContDiffAt ℝ ∞ G (χ x,g p):=chartCostCovector_contDiffAt
    (χ.map_source hx) (ψ.map_source hy) (by
      change ContMDiffAt _ _ ∞ (fun q:M×M=>cost q.1 q.2) (χ.symm (χ x),ψ.symm (ψ (riemannianExp x p)))
      rw [χ.left_inv hx,ψ.left_inv hy]
      exact cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M) hp)
  have hn:∀ᶠ v:E in 𝓝 p,v∈injectivityDomain x ∧ riemannianExp x v∈ψ.source:=by
    filter_upwards [(isOpen_injectivityDomain x).mem_nhds hp,
      (contMDiff_riemannianExp_fiber x p).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source b).mem_nhds hy)] with v hv hw
    exact ⟨hv,hw⟩
  have hsource:∀ᶠ h:E in 𝓝 0,riemannianExp x h∈χ.source:=
    (contMDiff_riemannianExp_fiber x 0).continuousAt.preimage_mem_nhds
      (by simpa only [riemannianExp_zero] using (isOpen_extChartAt_source a).mem_nhds hx)
  have he: (fun v:E => (G (χ x,g v)).comp T) =ᶠ[𝓝 p] (fun v:E => -(innerSL ℝ v)):=by
    filter_upwards [hn] with v hv
    have hcost:ContDiffAt ℝ ∞ (chartCost a (riemannianExp x v)) (χ x):=by
      have H:=cost_contMDiffAt_of_injectivityDomain
        (⟨x,v⟩:TangentBundle 𝓘(ℝ,Model n) M) hv.1
      have hi:ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm (χ x):=
        (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds (χ.map_source hx))
      have H':ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
          (fun q:M×M=>cost q.1 q.2) (χ.symm (χ x),riemannianExp x v):=by
        simpa only [χ.left_inv hx] using H
      exact (H'.comp (χ x) (hi.prodMk contMDiffAt_const)).contDiffAt
    have heq:(normalCost x v)=ᶠ[𝓝 (0:E)] ((chartCost a (riemannianExp x v)) ∘ f):=by
      filter_upwards [hsource] with h hh
      change cost (riemannianExp x h) (riemannianExp x v)=cost (χ.symm (χ (riemannianExp x h))) (riemannianExp x v)
      rw [χ.left_inv hh]
    have HD:HasFDerivAt ((chartCost a (riemannianExp x v)) ∘ f)
        ((fderiv ℝ (chartCost a (riemannianExp x v)) (χ x)).comp T) 0:=by
      apply HasFDerivAt.comp 0 _ (hf.differentiableAt (by simp)).hasFDerivAt
      simpa only [hf0] using (hcost.differentiableAt (by simp)).hasFDerivAt
    have HH: (fderiv ℝ (chartCost a (riemannianExp x v)) (χ x)).comp T= -(innerSL ℝ v):=by
      rw [←HD.fderiv,←heq.fderiv_eq,(normalCost_hasFDerivAt_zero hv.1).fderiv]
      simp only [map_neg]
    change (fderiv ℝ (chartCost a (ψ.symm (ψ (riemannianExp x v)))) (χ x)).comp T=_
    rw [ψ.left_inv hv.2]
    exact HH
  have hmap:HasFDerivAt (fun v:E => (χ x,g v))
      ((0:E →L[ℝ] Model n).prod S) p:=
    (hasFDerivAt_const (χ x) p).prodMk (hg.differentiableAt (by simp)).hasFDerivAt
  have hd:=((hgc.differentiableAt (by simp)).hasFDerivAt.comp p hmap).clm_comp
    (hasFDerivAt_const T p)
  have hr:HasFDerivAt (fun v:E => -(innerSL ℝ v)) (-(innerSL ℝ)) p:=
    (innerSL ℝ).hasFDerivAt.neg
  have hde:= (hd.congr_of_eventuallyEq he.symm).unique hr
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  have H:=congrArg (fun A:E →L[ℝ] E →L[ℝ] ℝ=>A d e) hde
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.flip_apply,add_apply,zero_apply,zero_add,
    map_zero,neg_apply] at H
  change (fderiv ℝ G (χ x,g p)) (0,S d) (T e) = -inner ℝ d e at H
  change inner ℝ (T.adjoint ((mixedCostOperator a b (χ x) (g p)) (S d))) e=inner ℝ d e
  rw [ContinuousLinearMap.adjoint_inner_left,mixedCostOperator,bilinearOperator_inner]
  simpa only [mixedCostOperator,neg_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply,neg_eq_iff_eq_neg,G,innerSL_apply_apply] using H

end MixedIntrinsic
end WeakMTWTransport

end
end

end OAI
