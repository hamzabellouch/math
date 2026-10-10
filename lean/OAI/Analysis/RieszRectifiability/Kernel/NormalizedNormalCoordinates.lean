import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric

def tangentPlaneProjection {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (x : Ambient d) : Ambient d :=
  a + L (L.toContinuousLinearMap.adjoint (x - a))

def normalizedNormalHeight {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (x : Ambient d) : Ambient q :=
  δ⁻¹ • N.toContinuousLinearMap.adjoint (x - a)

theorem tangentPlaneProjection_continuous {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) : Continuous (tangentPlaneProjection a L) := by
  unfold tangentPlaneProjection
  fun_prop

theorem normalizedNormalHeight_continuous {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) : Continuous (normalizedNormalHeight a N δ) := by
  unfold normalizedNormalHeight
  fun_prop

theorem normalizedNormalHeight_reconstruct {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (hδ : δ ≠ 0) (x : Ambient d) :
    δ • N (normalizedNormalHeight a N δ x) = N (N.toContinuousLinearMap.adjoint (x - a)) := by
  rw [normalizedNormalHeight, map_smul, smul_smul, mul_inv_cancel₀ hδ, one_smul]

theorem normal_coordinates_decomposition {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) + N (N.toContinuousLinearMap.adjoint y) = y)
    (δ : ℝ) (hδ : δ ≠ 0) (x : Ambient d) :
    x - a = L (L.toContinuousLinearMap.adjoint (x - a)) + δ • N (normalizedNormalHeight a N δ x) := by
  rw [normalizedNormalHeight_reconstruct a N δ hδ]
  exact (hsplit (x - a)).symm

theorem physical_projection_distance_eq {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) + N (N.toContinuousLinearMap.adjoint y) = y)
    (δ : ℝ) (hδ : 0 < δ) (x : Ambient d) :
    dist x (tangentPlaneProjection a L x) = δ * ‖normalizedNormalHeight a N δ x‖ := by
  have h := normal_coordinates_decomposition a L N hsplit δ hδ.ne' x
  have he : x - tangentPlaneProjection a L x = δ • N (normalizedNormalHeight a N δ x) := by
    unfold tangentPlaneProjection
    rw [← sub_sub]
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, N.norm_map]

end

end RieszRectifiability

end OAI
