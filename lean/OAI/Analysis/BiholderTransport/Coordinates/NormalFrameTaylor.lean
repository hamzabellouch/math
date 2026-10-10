import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.JetPullback
import OAI.Analysis.BiholderTransport.Coordinates.NormalPoleTaylor

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section NormalFrameTaylor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteNF (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance tangentCompleteNF (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

omit [Nonempty M] in
lemma chart_normal_pole_frame_identity {E:Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] {f:M → ℝ} {x y a:M}
    {r:TangentSpace 𝓘(ℝ,Model n) y} {q:TangentSpace 𝓘(ℝ,Model n) x}
    (B:E →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (hr:r∈injectivityDomain y) (hq:q∈injectivityDomain x)
    (hyx:riemannianExp y r=x) (hxy:riemannianExp x q=y)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {p:Model n} {A:Model n →L[ℝ] Model n}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hAe:HasQuadraticExpansion (fun h=>f ((extChartAt 𝓘(ℝ,Model n) a).symm
      (extChartAt 𝓘(ℝ,Model n) a y+h))) p A)
    {R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R q) (hR0:R q=0)
    (hRe:∀ᶠ v in 𝓝 q,riemannianExp y (R v)=riemannianExp x v) :
    let g:=fun h:E=>
      extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (q+B h))-extChartAt 𝓘(ℝ,Model n) a y
    ∀d,‖B d‖^2+secondJetPullback (innerSL ℝ p) ((innerSL ℝ).comp A)
      (fderiv ℝ g 0) (fderiv ℝ (fderiv ℝ g) 0) d d=
      inner ℝ (S (fderiv ℝ R q (B d))) (fderiv ℝ R q (B d))+
        normalHessian y r (fderiv ℝ R q (B d)) (fderiv ℝ R q (B d)) := by
  dsimp only
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let g:=fun h:E=>χ (riemannianExp x (q+B h))-χ y
  have hg0:g 0=0:=by simp only [g,map_zero,add_zero,hxy,sub_self]
  have hchart:ContDiffAt ℝ ∞ (fun v:TangentSpace 𝓘(ℝ,Model n) x=>χ (riemannianExp x v)) q:=by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_extChartAt' (x:=a) (by simpa only [hxy,extChartAt_source] using hy)).comp q
      (contMDiff_riemannianExp_fiber x q)
  have hg:ContDiffAt ℝ 2 g 0:=by
    apply ContDiffAt.of_le _ (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hc : ContDiffAt ℝ ∞ (fun v:TangentSpace 𝓘(ℝ,Model n) x=>χ (riemannianExp x v)) (q+B 0) := by
      simpa only [map_zero,add_zero] using hchart
    exact (hc.comp 0 (contDiffAt_const.add B.contDiff.contDiffAt)).sub contDiffAt_const
  have H:=quadratic_expansion_comp_proxy hAe hg hg0
  simp only [add_zero] at H
  let P:=quadraticTaylor (f (χ.symm (χ y))) p A
  have he:HasSecondTaylor (fun h=>f (riemannianExp x (q+B h)))
      (fderiv ℝ (fun h=>P (g h)) 0) (fderiv ℝ (fderiv ℝ (fun h=>P (g h))) 0):=by
    apply H.congr_of_eventuallyEq
    have ht:ContinuousAt (fun h:E=>riemannianExp x (q+B h)) 0:=
      (contMDiff_riemannianExp_fiber x).continuous.continuousAt.comp (continuousAt_const.add B.continuous.continuousAt)
    have hh:=ht.eventually ((isOpen_extChartAt_source a).mem_nhds (by simpa only [map_zero,add_zero,hxy] using hy))
    filter_upwards [hh] with h hh
    change f (riemannianExp x (q+B h))=f (χ.symm (χ y+(χ (riemannianExp x (q+B h))-χ y)))
    rw [show χ y+(χ (riemannianExp x (q+B h))-χ y)=χ (riemannianExp x (q+B h)) by abel,χ.left_inv hh]
  have hn:ContDiffAt ℝ 2 (fun h:E=>‖q+B h‖^2/2) 0:=
    (half_norm_sq_contDiff.comp (contDiff_const.add B.contDiff)).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HT:=he.add (hasSecondTaylor_of_contDiffAt hn)
  have HT2:=(normal_stationary_pole_taylor hr hq hyx hS hR hR0 hRe).comp_stationary B.hasFDerivAt (map_zero B)
  intro d
  have HH:=HT.diagonal_unique' HT2 d
  rw [quadratic_proxy_pullback hA hg hg0] at HH
  simp only [add_apply,ContinuousLinearMap.comp_apply] at HH
  have hshift: fderiv ℝ (fderiv ℝ (fun h:E=>‖q+B h‖^2/2)) 0 d d=‖B d‖^2:=by
    have hf:ContDiffAt ℝ 2 (fun v:TangentSpace 𝓘(ℝ,Model n) x=>‖v‖^2/2) (q+B 0) :=
      half_norm_sq_contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    simpa only [ContinuousLinearMap.id_apply,half_norm_sq_second_fderiv,innerSL_apply_apply,real_inner_self_eq_norm_sq] using
      second_fderiv_comp_affine B q 0 hf d d
  rw [hshift] at HH
  change secondJetPullback (innerSL ℝ p) ((innerSL ℝ).comp A)
    (fderiv ℝ g 0) (fderiv ℝ (fderiv ℝ g) 0) d d+‖B d‖^2=
    inner ℝ (S (fderiv ℝ R q (B d))) (fderiv ℝ R q (B d))+
    normalHessian y r (fderiv ℝ R q (B d)) (fderiv ℝ R q (B d)) at HH
  linarith only [HH]
end NormalFrameTaylor
end WeakMTWTransport

end
end

end OAI
