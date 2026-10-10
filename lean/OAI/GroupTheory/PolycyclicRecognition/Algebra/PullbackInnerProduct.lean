import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! # Pulling an inner product back through a linear equivalence -/

noncomputable section
namespace PolycyclicRecognition

open Bornology Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def pullbackInner (A : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp A A

theorem contDiff_pullbackInner : ContDiff ℝ ∞ (pullbackInner (E := E) (F := F)) := by
  let B : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  change ContDiff ℝ ∞ (fun A : E →L[ℝ] F => ((B.comp A).flip.comp A).flip)
  have h₁ : ContDiff ℝ ∞ (fun A : E →L[ℝ] F =>
      B.comp A) :=
    contDiff_const.clm_comp contDiff_id
  let flipEF : (E →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E F ℝ).toLinearIsometry.toContinuousLinearMap
  let flipEE : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  have hfEF : ContDiff ℝ ∞ flipEF :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] F →L[ℝ] ℝ)
      (F := F →L[ℝ] E →L[ℝ] ℝ) flipEF
  have hfEE : ContDiff ℝ ∞ flipEE :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) flipEE
  have h₂ : ContDiff ℝ ∞ (fun A : E →L[ℝ] F => (B.comp A).flip) :=
    hfEF.comp h₁
  have h₃ := h₂.clm_comp contDiff_id
  exact hfEE.comp h₃

theorem pullbackInner_pos (A : E ≃L[ℝ] F) (v : E) (hv : v ≠ 0) :
    0 < pullbackInner A.toContinuousLinearMap v v := by
  apply real_inner_self_pos.mpr
  exact fun h => hv (A.injective (h.trans (map_zero A).symm))

theorem pullbackInner_bounded (A : E ≃L[ℝ] F) :
    IsVonNBounded ℝ {v : E | pullbackInner A.toContinuousLinearMap v v < 1} := by
  apply ((NormedSpace.isVonNBounded_ball ℝ F 1).image A.symm.toContinuousLinearMap).subset
  intro v hv
  change pullbackInner A.toContinuousLinearMap v v < 1 at hv
  refine ⟨A v, ?_, A.symm_apply_apply v⟩
  rw [Metric.mem_ball, dist_zero_right]
  have h : ‖A v‖ ^ 2 < 1 := by
    simpa only [pullbackInner, ContinuousLinearMap.bilinearComp_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, ContinuousLinearEquiv.coe_coe] using hv
  nlinarith [norm_nonneg (A v)]

end PolycyclicRecognition

end

end OAI
