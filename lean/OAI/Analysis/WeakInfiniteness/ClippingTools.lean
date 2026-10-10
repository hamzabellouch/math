import Mathlib
import OAI.Analysis.WeakInfiniteness.Clipping

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma norm_clip_sub_le {T W : B} {δ : ℝ} (hδ : 0 ≤ δ)
    (hW : ‖W‖ ≤ 1) (hTW : ‖T-W‖ ≤ δ) : ‖cstarClip T-W‖ ≤ 2*δ := by
  have hT : ‖T‖ ≤ 1+δ := (norm_le_norm_add_norm_sub' T W).trans (add_le_add hW hTW)
  have hc : ‖T-cstarClip T‖ ≤ δ :=
    (norm_sub_cstarClip_le T).trans (max_le (by linarith) hδ)
  calc
    ‖cstarClip T-W‖ ≤ ‖cstarClip T-T‖+‖T-W‖ := by
      simpa only [dist_eq_norm] using dist_triangle (cstarClip T) T W
    _ ≤ δ+δ := by rw [norm_sub_rev (cstarClip T) T]; exact add_le_add hc hTW
    _ = 2*δ := by ring

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
lemma isometry_intertwiner_error_le (T W : K →L[ℂ] K) (D : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (hW : W.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D) :
    ‖T.comp J.toContinuousLinearMap-J.toContinuousLinearMap.comp D‖ ≤ ‖T-W‖ := by
  rw [← hW, ← ContinuousLinearMap.sub_comp]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hn : ‖J.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖J x‖ ≤ 1*‖x‖
    rw [J.norm_map, one_mul]
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _)

lemma clip_reducing_models (T W : K →L[ℂ] K) (D : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) {δ : ℝ} (hδ : 0 ≤ δ) (hW : ‖W‖ ≤ 1) (hTW : ‖T-W‖ ≤ δ)
    (hr : W.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D)
    (hra : (star W).comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp (star D)) :
    ‖(cstarClip T).comp J.toContinuousLinearMap-J.toContinuousLinearMap.comp D‖ ≤ 2*δ ∧
    ‖(star (cstarClip T)).comp J.toContinuousLinearMap-J.toContinuousLinearMap.comp (star D)‖ ≤ 2*δ := by
  have hnorm := norm_clip_sub_le hδ hW hTW
  constructor
  · exact (isometry_intertwiner_error_le _ _ _ J hr).trans hnorm
  · apply (isometry_intertwiner_error_le _ _ _ J hra).trans
    rwa [← star_sub, norm_star]

end

end WeakPureInfiniteness
end

end OAI
