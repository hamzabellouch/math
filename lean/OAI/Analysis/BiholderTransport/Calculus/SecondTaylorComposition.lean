import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ShortEnvelopeJetTest
import OAI.Analysis.BiholderTransport.Calculus.ScalarJetFormula
import OAI.Analysis.BiholderTransport.Calculus.TaylorPositivity

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma HasSecondTaylor.diagonal_unique {f:E → ℝ} {l:E →L[ℝ] ℝ}
    {B C:E →L[ℝ] E →L[ℝ] ℝ} (hB:HasSecondTaylor f l B) (hC:HasSecondTaylor f l C) (d:E) :
    B d d=C d d := by
  have h1:HasSecondTaylor (fun h=>f h-f h) 0 (B-C):=by simpa only [sub_self] using hB.sub hC
  have h2:HasSecondTaylor (fun h=>f h-f h) 0 (C-B):=by simpa only [sub_self] using hC.sub hB
  have hm:IsLocalMin (fun h=>f h-f h) 0:=by
    exact Eventually.of_forall (fun h=>by simp)
  have H1:=h1.nonneg_of_localMin hm d
  have H2:=h2.nonneg_of_localMin hm d
  simp only [sub_apply] at H1 H2
  linarith

lemma HasSecondTaylor.congr_of_eventuallyEq {f g:E → ℝ} {l:E →L[ℝ] ℝ}
    {B:E →L[ℝ] E →L[ℝ] ℝ} (hf:HasSecondTaylor f l B) (he:g=ᶠ[𝓝 0] f) :
    HasSecondTaylor g l B := by
  have h0:=he.self_of_nhds
  apply hf.congr' _ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [he] with h hh
  rw [hh,h0]

lemma HasQuadraticExpansion.hasSecondTaylor' {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) :
    HasSecondTaylor f (innerSL ℝ p) ((innerSL ℝ).comp A) := by
  have H:=quadratic_expansion_polynomial_remainder hf
  unfold HasSecondTaylor
  convert H using 1
  funext h
  simp only [quadraticTaylor,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
  ring

lemma quadratic_expansion_comp_proxy {f:F → ℝ} {p:F} {A:F →L[ℝ] F}
    (hf:HasQuadraticExpansion f p A) {g:E → F} (hg:ContDiffAt ℝ 2 g 0) (hg0:g 0=0) :
    let P:=quadraticTaylor (f 0) p A
    HasSecondTaylor (fun h=>f (g h)) (fderiv ℝ (fun h=>P (g h)) 0)
      (fderiv ℝ (fderiv ℝ (fun h=>P (g h))) 0) := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P:=by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hQ:ContDiffAt ℝ 2 (fun h=>P (g h)) 0:=hP.contDiffAt.comp 0 hg
  apply (hasSecondTaylor_of_contDiffAt hQ).of_littleO_difference
  · simp only [hg0,P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  · have hgd:HasFDerivAt g (fderiv ℝ g 0) 0:=(hg.differentiableAt (by norm_num)).hasFDerivAt
    have ht:Tendsto g (𝓝 0) (𝓝 0):=hg0 ▸ hg.continuousAt.tendsto
    have hO:(fun h:E=>‖g h‖)=O[𝓝 0] (fun h=>‖h‖):=by
      simpa only [hg0,sub_zero] using hgd.isBigO_sub.norm_left.norm_right
    exact ((quadratic_expansion_polynomial_remainder hf).comp_tendsto ht).trans_isBigO (hO.pow 2)

lemma quadratic_proxy_pullback {f0:ℝ} {p:F} {A:F →L[ℝ] F}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    {g:E → F} (hg:ContDiffAt ℝ 2 g 0) (hg0:g 0=0) :
    fderiv ℝ (fderiv ℝ (fun h=>quadraticTaylor f0 p A (g h))) 0=
      secondJetPullback (innerSL ℝ p) ((innerSL ℝ).comp A)
        (fderiv ℝ g 0) (fderiv ℝ (fderiv ℝ g) 0) := by
  have hP:ContDiff ℝ 2 (quadraticTaylor f0 p A):=by
    change ContDiff ℝ 2 (fun h:F=>f0+inner ℝ p h+inner ℝ (A h) h/2)
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  ext d e
  rw [second_fderiv_comp_at (Eventually.of_forall (fun _=>hP.differentiable (by norm_num) _))
    (((hP.contDiffAt.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))) hg]
  rw [hg0,quadraticTaylor_second_fderiv f0 p hA]
  rw [show fderiv ℝ (quadraticTaylor f0 p A) 0=innerSL ℝ p from by
    simpa only [map_zero,add_zero] using (quadraticTaylor_hasFDerivAt f0 p hA 0).fderiv]
  rfl
end WeakMTWTransport

end

end OAI
