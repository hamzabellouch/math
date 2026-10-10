import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeLinearSandwich

namespace OAI

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_derivative_source_slice {B : E×F → ℝ} {a : E} {b : F}
    (hB : ContDiffAt ℝ 2 B (a,b)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun x => B (x,b))) a v w =
      fderiv ℝ (fderiv ℝ B) (a,b) (v,0) (w,0) := by
  let L : E →L[ℝ] E×F := inl ℝ E F
  let C : E×F → ℝ := fun z => B (z+(0,b))
  have hC : ContDiffAt ℝ 2 C (L a) := by
    have hB' : ContDiffAt ℝ 2 B (L a+(0,b)) := by
      simpa only [L,inl_apply,Prod.mk_add_mk,add_zero,zero_add] using hB
    exact hB'.comp (L a) (contDiffAt_id.add contDiffAt_const)
  have h := second_derivative_linear_sandwich L (ContinuousLinearMap.id ℝ ℝ) hC v w
  have heq : fderiv ℝ C =ᶠ[𝓝 (a,0)] fun z => fderiv ℝ B (z+(0,b)) := by
    filter_upwards [((continuousAt_id.add_const (0,b)).eventually
      (show ∀ᶠ z in 𝓝 ((a,0)+(0,b)), ContDiffAt ℝ 2 B z from by
        simpa only [Prod.mk_add_mk,add_zero,zero_add] using hB.eventually (by norm_num)))] with z hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (0,b))).fderiv
  have hD := ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD' : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) (a,b)) ((a,0)+(0,b)) := by
    simpa using hD
  have hDc := hD'.comp (a,0) ((hasFDerivAt_id (a,(0:F))).add_const (0,b))
  have hDD := (hDc.congr_of_eventuallyEq heq).fderiv
  have hh : fderiv ℝ (fderiv ℝ C) (a,0)=fderiv ℝ (fderiv ℝ B) (a,b) := by
    simpa only [comp_id] using hDD
  have hh' : fderiv ℝ (fderiv ℝ (fun x => B (x,b))) a v w =
      fderiv ℝ (fderiv ℝ C) (a,0) (v,0) (w,0) := by
    simpa only [id_apply,C,L,inl_apply,Prod.mk_add_mk,add_zero,zero_add] using h
  exact hh'.trans (congrArg (fun K : E×F →L[ℝ] E×F →L[ℝ] ℝ => K (v,0) (w,0)) hh)

lemma hasDerivAt_source_hessian_line {B : E×F → ℝ} {a v : E} {b w : F} {t : ℝ}
    (hB : ContDiffAt ℝ 3 B (a,b)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ
      (fun x => B (x,b+(s-t) • w))) a v v)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,b) (0,w) (v,0) (v,0)) t := by
  let q : ℝ → E×F := fun s => (a,b+(s-t) • w)
  have hq : HasDerivAt q (0,w) t := by
    simpa only [q,one_smul,id_eq] using (hasDerivAt_const t a).prodMk
      (((hasDerivAt_id t).sub_const t).smul_const w |>.const_add b)
  have hqt : q t=(a,b) := by simp [q]
  have hH := ((hB.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH' : HasFDerivAt (fderiv ℝ (fderiv ℝ B))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,b)) (q t) := hqt.symm ▸ hH.hasFDerivAt
  have hD := hH'.comp_hasDerivAt (f := q) (l := fderiv ℝ (fderiv ℝ B)) t hq
  have hD' := (hD.clm_apply (hasDerivAt_const t (v,(0:F)))).clm_apply
    (hasDerivAt_const t (v,(0:F)))
  have heq : (fun s : ℝ => fderiv ℝ (fderiv ℝ
      (fun x => B (x,b+(s-t) • w))) a v v) =ᶠ[𝓝 t]
      fun s => fderiv ℝ (fderiv ℝ B) (q s) (v,0) (v,0) := by
    filter_upwards [hq.continuousAt.eventually
      (show ∀ᶠ z in 𝓝 (q t), ContDiffAt ℝ 3 B z from by
        rw [hqt]; exact hB.eventually (by norm_num))] with s hs
    exact second_derivative_source_slice (hs.of_le (by norm_num)) v v
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  simpa only [Function.comp_apply,zero_add,add_zero,map_zero] using hD'

end WeakMTWTransport

end



noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma second_derivative_target_slice {B : E×F → ℝ} {a : E} {b : F}
    (hB : ContDiffAt ℝ 2 B (a,b)) (v w : F) :
    fderiv ℝ (fderiv ℝ (fun y => B (a,y))) b v w =
      fderiv ℝ (fderiv ℝ B) (a,b) (0,v) (0,w) := by
  let L : F →L[ℝ] E×F := inr ℝ E F
  let C : E×F → ℝ := fun z => B (z+(a,0))
  have hC : ContDiffAt ℝ 2 C (L b) := by
    have hB' : ContDiffAt ℝ 2 B (L b+(a,0)) := by
      simpa only [L,inr_apply,Prod.mk_add_mk,add_zero,zero_add] using hB
    exact hB'.comp (L b) (contDiffAt_id.add contDiffAt_const)
  have h := second_derivative_linear_sandwich L (ContinuousLinearMap.id ℝ ℝ) hC v w
  have heq : fderiv ℝ C =ᶠ[𝓝 (0,b)] fun z => fderiv ℝ B (z+(a,0)) := by
    filter_upwards [((continuousAt_id.add_const (a,0)).eventually
      (show ∀ᶠ z in 𝓝 ((0,b)+(a,0)), ContDiffAt ℝ 2 B z from by
        simpa only [Prod.mk_add_mk,add_zero,zero_add] using hB.eventually (by norm_num)))] with z hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (a,0))).fderiv
  have hD := ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD' : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) (a,b)) ((0,b)+(a,0)) := by
    simpa using hD
  have hDc := hD'.comp ((0:E),b) ((hasFDerivAt_id ((0:E),b)).add_const (a,0))
  have hDD := (hDc.congr_of_eventuallyEq heq).fderiv
  have hh : fderiv ℝ (fderiv ℝ C) (0,b)=fderiv ℝ (fderiv ℝ B) (a,b) := by
    simpa only [comp_id] using hDD
  have hh' : fderiv ℝ (fderiv ℝ (fun y => B (a,y))) b v w =
      fderiv ℝ (fderiv ℝ C) (0,b) (0,v) (0,w) := by
    simpa only [id_apply,C,L,inr_apply,Prod.mk_add_mk,add_zero,zero_add] using h
  exact hh'.trans (congrArg (fun K : E×F →L[ℝ] E×F →L[ℝ] ℝ => K (0,v) (0,w)) hh)
end WeakMTWTransport

end

end OAI
