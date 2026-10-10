import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.FullSet

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_affine {f : F → ℝ} (L : E →L[ℝ] F) (b : F) (x : E)
    (hf : ContDiffAt ℝ 2 f (b+L x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun h => f (b+L h))) x v w =
      fderiv ℝ (fderiv ℝ f) (b+L x) (L v) (L w) := by
  have hL : ∀ y:E, HasFDerivAt (fun h : E => b+L h) L y :=
    fun y => (L.hasFDerivAt (x := y)).const_add b
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun h : E => b+L h) x (hL x)
  have H := hd.clm_comp (hasFDerivAt_const L x)
  have heq : (fun h => fderiv ℝ f (b+L h) |>.comp L) =ᶠ[𝓝 x]
      (fderiv ℝ (fun h => f (b+L h))) := by
    have hn := (hL x).continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hn] with h hh
    exact ((hh.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun h : E => b+L h) h (hL h)).fderiv.symm
  have he := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w)
    (H.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,map_zero,ContinuousLinearMap.comp_zero,
    zero_add,add_apply,zero_apply] using he

lemma hasSecondTaylor_shift {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    HasSecondTaylor (fun h => f (x+h)) (fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) x) := by
  have hc : ContDiffAt ℝ 2 (fun h => f (x+h)) 0 := by
    exact (show ContDiffAt ℝ 2 f (x+(0:E)) by simpa using hf).comp 0
      (contDiffAt_const.add contDiffAt_id)
  have H := hasSecondTaylor_of_contDiffAt hc
  have hD : fderiv ℝ (fun h => f (x+h)) 0=fderiv ℝ f x := by
    have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt
    have hl := (hasFDerivAt_id (𝕜 := ℝ) (0:E)).const_add x
    simpa only [add_zero,ContinuousLinearMap.comp_id,Function.comp_def] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:E)) by simpa using hd).comp
        (f := fun h : E => x+h) 0 hl).fderiv
  have hDD : fderiv ℝ (fderiv ℝ (fun h => f (x+h))) 0=
      fderiv ℝ (fderiv ℝ f) x := by
    ext v w
    simpa only [ContinuousLinearMap.id_apply,add_zero] using
      second_fderiv_comp_affine (ContinuousLinearMap.id ℝ E) x 0
        (by simpa using hf) v w
  rwa [hD,hDD] at H

end

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma half_norm_sq_hasFDerivAt (p : E) :
    HasFDerivAt (fun v : E => ‖v‖^2/2) (innerSL ℝ p) p := by
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_smul (1/2:ℝ)
  convert! H using 1
  · ext v; simp only [Pi.smul_apply,smul_eq_mul,id_eq]; ring
  · ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      smul_apply,smul_eq_mul,innerSL_apply_apply,id_eq]
    ring

lemma half_norm_sq_fderiv :
    fderiv ℝ (fun v : E => ‖v‖^2/2) = innerSL ℝ := by
  funext p
  exact (half_norm_sq_hasFDerivAt p).fderiv

lemma half_norm_sq_second_fderiv (p a d : E) :
    fderiv ℝ (fderiv ℝ (fun v : E => ‖v‖^2/2)) p a d=inner ℝ a d := by
  rw [half_norm_sq_fderiv]
  rw [(innerSL ℝ).hasFDerivAt.fderiv]
  rfl

lemma half_norm_sq_contDiff : ContDiff ℝ ∞ (fun v : E => ‖v‖^2/2) := by
  simpa only [one_div,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    ((contDiff_norm_sq (𝕜 := ℝ) (E := E) (n := ∞)).const_smul (1/2:ℝ))

lemma norm_square_hasSecondTaylor (p : E) :
    HasSecondTaylor (fun h : E => ‖p+h‖^2/2) (innerSL ℝ p) (innerSL ℝ) := by
  have hc : ContDiffAt ℝ 2 (fun v : E => ‖v‖^2/2) p :=
    ((half_norm_sq_contDiff (E := E)).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have H := hasSecondTaylor_shift hc
  simpa only [half_norm_sq_fderiv,(innerSL ℝ).hasFDerivAt.fderiv] using H

end WeakMTWTransport

end

end OAI
