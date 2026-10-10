import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.FullSet

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pullBilinear (B : F →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)

@[simp] lemma pullBilinear_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F)
    (u v : E) : pullBilinear B A u v=B (A u) (A v) := rfl

lemma HasSecondTaylor.comp_linear {f : F → ℝ} {l : F →L[ℝ] ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (A : E →L[ℝ] F) :
    HasSecondTaylor (fun h => f (A h)) (l.comp A) (pullBilinear B A) := by
  have H := (hf.comp_tendsto (show Tendsto A (𝓝 0) (𝓝 0) by
    simpa only [ContinuousAt,map_zero] using (A.continuous.continuousAt (x := (0:E))))).trans_isBigO
      ((A.isBigO_id (𝓝 0)).norm_left.norm_right.pow 2)
  simpa only [HasSecondTaylor,map_zero,Function.comp_def,ContinuousLinearMap.comp_apply,
    pullBilinear_apply] using H

lemma HasSecondTaylor.sub_linear {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) :
    HasSecondTaylor (fun h => f h-l h) 0 B := by
  unfold HasSecondTaylor at *
  have heq : (fun h => f h-l h-(f 0-l 0)-(0 : E →L[ℝ] ℝ) h-B h h/2) =
      (fun h => f h-f 0-l h-B h h/2) := by
    funext h; simp only [map_zero,sub_zero,zero_apply]; ring
  rw [heq]; exact hf

def HasLowerSecondTaylor (f : E → ℝ) (l : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0:E), f 0+l h+B h h/2-ε*‖h‖^2≤f h

lemma HasLowerSecondTaylor.mono {f g : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f l B)
    (he : f 0=g 0) (hle : f≤ᶠ[𝓝 0] g) : HasLowerSecondTaylor g l B := by
  intro ε hε
  filter_upwards [hf ε hε,hle] with h hh hfg
  rw [←he]
  exact hh.trans hfg

lemma HasLowerSecondTaylor.of_positive_mul {f : E → ℝ} {m : ℝ} (hm : 0 < m)
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor (fun h => m * f h) l B) :
    HasLowerSecondTaylor f (m⁻¹ • l) (m⁻¹ • B) := by
  intro ε hε
  filter_upwards [hf (m*ε) (mul_pos hm hε)] with h hh
  apply (mul_le_mul_iff_right₀ hm).mp
  simpa only [smul_apply,smul_eq_mul,mul_sub,mul_add,
    mul_div_assoc,←mul_assoc,mul_inv_cancel₀ hm.ne',one_mul] using hh

lemma lowerTaylor_of_stationary_transfer {S : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hS : HasSecondTaylor S 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0)
    {f : E → ℝ} {l : E →L[ℝ] ℝ} {C : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasSecondTaylor f l C)
    {ψ : E → ℝ} {m : ℝ} (hm : 0 < m)
    (hle : ∀ᶠ h in 𝓝 (0:E),
      S (a h)-S 0-(f h-f 0-l h)≤ m * (ψ h-ψ 0)) :
    HasLowerSecondTaylor ψ 0 (m⁻¹ • (pullBilinear B A-C)) := by
  have hcomp := (hS.comp_stationary ha ha0).sub hf.sub_linear
  have hE : ∀ h:E, (S (a h)-(f h-l h))-(S (a 0)-(f 0-l 0)) =
      S (a h)-S 0-(f h-f 0-l h) := by
    intro h; rw [ha0,map_zero]; ring
  have hlow : HasLowerSecondTaylor (fun h => m * ψ h) 0 (pullBilinear B A-C) := by
    intro ε hε
    filter_upwards [hcomp.eventually hε,hle] with h hh hbound
    have hh' : |(S (a h)-(f h-l h))-(S (a 0)-(f 0-l 0))-
        (pullBilinear B A-C) h h/2|≤ε*‖h‖^2 := by
      simpa only [zero_sub,sub_zero,zero_apply,pullBilinear] using hh
    rw [hE] at hh'
    simp only [zero_apply,add_zero]
    have H := (abs_le.mp hh').1
    nlinarith
  simpa only [smul_zero] using hlow.of_positive_mul hm

end WeakMTWTransport

end

end OAI
