import Mathlib
import OAI.Geometry.Borsuk.Simplicial.UnitRadial

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
open SimplicialChains
section HemisphereChart
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (w : E) (e : W →ₗᵢ[ℝ] E)
noncomputable def hemisphereChart (v : W) : E := unitRadial (w + e v)
noncomputable def hemisphereInverse (u : E) : W := ⟪w,u⟫⁻¹ • e.toContinuousLinearMap.adjoint u

lemma adjoint_isometry_apply (v : W) : e.toContinuousLinearMap.adjoint (e v) = v := by
  have hh := congrArg (fun T : W →L[ℝ] W => T v) e.adjoint_comp_self
  exact hh

lemma adjoint_normal (he : ∀ v, ⟪w,e v⟫ = 0) : e.toContinuousLinearMap.adjoint w = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_zero_left,ContinuousLinearMap.adjoint_inner_left]
  exact he v

lemma frame_decomposition (hw : ‖w‖ = 1)
    (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (u : E) :
    e (e.toContinuousLinearMap.adjoint u) = u - ⟪w,u⟫ • w := by
  obtain ⟨v,hv⟩ := hes (u - ⟪w,u⟫ • w) (by simp [inner_sub_right,inner_smul_right,hw])
  have ha := congrArg e.toContinuousLinearMap.adjoint hv
  rw [adjoint_isometry_apply,map_sub,map_smul,adjoint_normal w e he,smul_zero,sub_zero] at ha
  rw [← ha,hv]

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphere_add_ne_zero (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    w + e v ≠ 0 := by
  intro hz
  have h := congrArg (fun u => ⟪w,u⟫) hz
  simp [inner_add_right,he,hw] at h

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_contDiff (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (hemisphereChart w e) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun v => w + e v) := contDiff_const.add e.contDiff
  exact (hc.norm ℝ (hemisphere_add_ne_zero w e hw he)).inv
    (fun v => norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)) |>.smul hc

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_norm (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    ‖hemisphereChart w e v‖ = 1 := unitRadial_norm (hemisphere_add_ne_zero w e hw he v)

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_inner_pos (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    0 < ⟪w,hemisphereChart w e v⟫ := by
  simp only [hemisphereChart,unitRadial,inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq,hw,one_pow,he,add_zero,mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr (hemisphere_add_ne_zero w e hw he v))

lemma hemisphereInverse_chart (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    hemisphereInverse w e (hemisphereChart w e v) = v := by
  have hn : ‖w + e v‖ ≠ 0 := norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)
  simp only [hemisphereInverse,hemisphereChart,unitRadial,inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq,hw,one_pow,he,add_zero,mul_one,inv_inv,map_smul,map_add,
    adjoint_normal w e he,adjoint_isometry_apply,zero_add,smul_smul,mul_inv_cancel₀ hn,one_smul]

lemma hemisphereChart_inverse (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {u : E} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫) :
    hemisphereChart w e (hemisphereInverse w e u) = u := by
  have heq : w + e (hemisphereInverse w e u) = ⟪w,u⟫⁻¹ • u := by
    rw [hemisphereInverse,map_smul,frame_decomposition w e hw he hes,smul_sub,smul_smul,
      inv_mul_cancel₀ (ne_of_gt hwu),one_smul]
    abel
  rw [hemisphereChart,heq,unitRadial,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hwu),hu,mul_one,inv_inv,smul_smul,
    mul_inv_cancel₀ (ne_of_gt hwu),one_smul]

lemma hemisphereInverse_continuousOn :
    ContinuousOn (hemisphereInverse w e) {u | 0 < ⟪w,u⟫} :=
  ((continuous_const.inner continuous_id).continuousOn.inv₀ (fun _ h => ne_of_gt h)).smul
    e.toContinuousLinearMap.adjoint.continuous.continuousOn
end HemisphereChart
end BorsukNine

end OAI
