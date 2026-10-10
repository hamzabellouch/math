import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma second_derivative_linear_sandwich {f : F → G} {a : E}
    (L : E →L[ℝ] F) (K : G →L[ℝ] H) (hf : ContDiffAt ℝ 2 f (L a)) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => K (f (L x)))) a u v =
      K (fderiv ℝ (fderiv ℝ f) (L a) (L u) (L v)) := by
  have heq : fderiv ℝ (fun x => K (f (L x))) =ᶠ[𝓝 a]
      fun x => K.comp ((fderiv ℝ f (L x)).comp L) := by
    filter_upwards [L.continuous.continuousAt.eventually (hf.eventually (by norm_num))] with x hx
    exact (K.hasFDerivAt.comp x ((hx.differentiableAt (by norm_num)).hasFDerivAt.comp x
      L.hasFDerivAt)).fderiv
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD := (hasFDerivAt_const K a).clm_comp
    ((hdd.hasFDerivAt.comp a L.hasFDerivAt).clm_comp (hasFDerivAt_const L a))
  have h := congrArg (fun A : E →L[ℝ] E →L[ℝ] H => A u v)
    ((hD.congr_of_eventuallyEq heq).fderiv)
  simpa only [comp_apply,compL_apply,flip_apply,add_apply,zero_apply,map_zero,zero_add,add_zero] using h

end WeakMTWTransport

end



noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma second_derivative_half_norm_sq {g : E → F} {a v : E}
    (hg : ContDiffAt ℝ 2 g a) :
    fderiv ℝ (fderiv ℝ (fun x => ‖g x‖^2/2)) a v v =
      ‖fderiv ℝ g a v‖^2 + inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v) := by
  let G : E → E →L[ℝ] ℝ := fun x => (innerSL ℝ (g x)).comp (fderiv ℝ g x)
  have hdg := hg.differentiableAt (by norm_num)
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG := ((innerSL ℝ).hasFDerivAt.comp a hdg.hasFDerivAt).clm_comp hddg.hasFDerivAt
  have heq : fderiv ℝ (fun x => ‖g x‖^2/2) =ᶠ[𝓝 a] G := by
    filter_upwards [hg.eventually (by norm_num : (2:ℕ∞ω)≠∞)] with x hx
    have hd0 := ((hx.differentiableAt (by norm_num)).hasFDerivAt.norm_sq).const_smul (1/2:ℝ)
    have hd := hd0.fderiv
    have hfun : (fun z => ‖g z‖^2/2)=(fun z => (1/2:ℝ) • ‖g z‖^2) := by
      funext z; simp only [smul_eq_mul]; ring
    rw [hfun]
    change fderiv ℝ ((1/2:ℝ) • fun z => ‖g z‖^2) x=G x
    rw [hd]
    ext w
    simp only [G,comp_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
    ring
  have hD := (hG.congr_of_eventuallyEq heq).fderiv
  rw [hD]
  simp only [comp_apply,compL_apply,add_apply,flip_apply]
  change inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v)+inner ℝ (fderiv ℝ g a v) (fderiv ℝ g a v)=_
  rw [real_inner_self_eq_norm_sq,add_comm]

lemma third_derivative_swap_outer {f : E → ℝ} {a u v w : E}
    (hf : ContDiffAt ℝ 3 f a) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a v u w := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num) |>.eq u v)

lemma third_derivative_swap_inner {f : E → ℝ} {a u v w : E}
    (hf : ContDiffAt ℝ 3 f a) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a u w v := by
  let H := fderiv ℝ (fderiv ℝ f)
  have hH := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvw := (hH.hasFDerivAt.clm_apply (hasFDerivAt_const v a)).clm_apply
    (hasFDerivAt_const w a)
  have hwv := (hH.hasFDerivAt.clm_apply (hasFDerivAt_const w a)).clm_apply
    (hasFDerivAt_const v a)
  have heq : (fun x => H x v w)=ᶠ[𝓝 a] (fun x => H x w v) := by
    filter_upwards [hf.eventually (by norm_num : (3:ℕ∞ω)≠∞)] with x hx
    exact hx.isSymmSndFDerivAt (by norm_num) |>.eq v w
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L u)
    ((hvw.congr_of_eventuallyEq heq.symm).unique hwv)
  simpa only [comp_apply,flip_apply,add_apply,zero_apply,map_zero,zero_add,add_zero] using hh

lemma eikonal_third_derivative {B : E×F → ℝ} {g : E → F} {a v : E}
    (hB : ContDiffAt ℝ 3 B (a,0)) (hg : ContDiffAt ℝ 2 g a)
    (heik : (fun x => B (x,0)) =ᶠ[𝓝 a] (fun x => ‖g x‖^2/2))
    (hgrad : ∀ᶠ x in 𝓝 a, ∀ w : F,
      fderiv ℝ B (x,0) (0,w)=inner ℝ (g x) w) :
    fderiv ℝ (fderiv ℝ B) (a,0) (v,0) (v,0) =
      ‖fderiv ℝ g a v‖^2+
        fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,0) (0,g a) (v,0) (v,0) := by
  let L := ContinuousLinearMap.inl ℝ E F
  have hL : L a=(a,0) := rfl
  have hsource := second_derivative_linear_sandwich L (ContinuousLinearMap.id ℝ ℝ)
    (show ContDiffAt ℝ 2 B (L a) from hB.of_le (by norm_num)) v v
  have hnorm := congrArg (fun D : E →L[ℝ] E →L[ℝ] ℝ => D v v)
    (heik.fderiv (𝕜 := ℝ)).fderiv_eq
  have hs : fderiv ℝ (fderiv ℝ B) (a,0) (v,0) (v,0)=
      ‖fderiv ℝ g a v‖^2+inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v) := by
    have hsource' : fderiv ℝ (fderiv ℝ (fun x => B (x,0))) a v v =
        fderiv ℝ (fderiv ℝ B) (a,0) (v,0) (v,0) := hsource
    rw [←hsource']
    exact hnorm.trans (second_derivative_half_norm_sq hg)
  have hpartial : (fun x => fderiv ℝ B (x,0) (0,g a)) =ᶠ[𝓝 a]
      fun x => inner ℝ (g a) (g x) := by
    filter_upwards [hgrad] with x hx
    rw [hx,real_inner_comm]
  have hp2 := congrArg (fun D : E →L[ℝ] E →L[ℝ] ℝ => D v v)
    (hpartial.fderiv (𝕜 := ℝ)).fderiv_eq
  have hleft := second_derivative_linear_sandwich L
    (ContinuousLinearMap.apply ℝ ℝ ((0:E),g a))
    (show ContDiffAt ℝ 2 (fderiv ℝ B) (L a) from hB.fderiv_right (by norm_num)) v v
  have hright := second_derivative_linear_sandwich (ContinuousLinearMap.id ℝ E)
    (innerSL ℝ (g a)) hg v v
  have htr : inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v)=
      fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,0) (v,0) (v,0) (0,g a) := by
    exact hright.symm.trans (hp2.symm.trans hleft)
  rw [hs,htr]
  congr 1
  rw [third_derivative_swap_inner hB,third_derivative_swap_outer hB]

end WeakMTWTransport

end

end OAI
