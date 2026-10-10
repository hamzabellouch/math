import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Function Metric

def affineGraphLinear {n q d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) :
    Ambient n →L[ℝ] Ambient d :=
  L.toContinuousLinearMap + δ • (N.toContinuousLinearMap.comp A)

def affineGraphPlane {n q d : ℕ} (a : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) :
    AffineSubspace ℝ (Ambient d) :=
  AffineSubspace.mk' (a + δ • N b) (affineGraphLinear L N A δ).toLinearMap.range

theorem affineGraphLinear_leftInverse {n q d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ)
    (horth : ∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) :
    LeftInverse L.toContinuousLinearMap.adjoint (affineGraphLinear L N A δ) := by
  intro t
  have hL : L.toContinuousLinearMap.adjoint (L t) = t :=
    DFunLike.congr_fun L.adjoint_comp_self t
  change L.toContinuousLinearMap.adjoint (L t + δ • N (A t)) = t
  rw [map_add, map_smul, hL, horth, smul_zero, add_zero]

theorem affineGraphPlane_direction_finrank {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ)
    (horth : ∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) :
    Module.finrank ℝ (affineGraphPlane a L N b A δ).direction = n := by
  rw [affineGraphPlane, AffineSubspace.direction_mk']
  rw [LinearMap.finrank_range_of_inj
    (affineGraphLinear_leftInverse L N A δ horth).injective]
  exact finrank_euclideanSpace_fin

theorem affineGraphPoint_mem {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) (t : Ambient n) :
    a + L t + δ • N (b + A t) ∈ affineGraphPlane a L N b A δ := by
  rw [affineGraphPlane, AffineSubspace.mem_mk']
  refine ⟨t, ?_⟩
  change L t + δ • N (A t) = a + L t + δ • N (b + A t) - (a + δ • N b)
  rw [map_add, smul_add]
  abel

theorem affineGraphPlane_infDist_le {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ)
    (x : Ambient d) (t : Ambient n) (s : Ambient q) (hx : x - a = L t + N s) :
    infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) ≤ ‖s - δ • (b + A t)‖ := by
  have hdist : dist x (a + L t + δ • N (b + A t)) = ‖s - δ • (b + A t)‖ := by
    rw [dist_eq_norm]
    have hdiff : x - (a + L t + δ • N (b + A t)) = N (s - δ • (b + A t)) := by
      rw [map_sub, map_smul]
      have heq : x = a + L t + N s := by rw [add_assoc, ← hx]; abel
      rw [heq]
      abel
    rw [hdiff, N.norm_map]
  exact (infDist_le_dist_of_mem (affineGraphPoint_mem a L N b A δ t)).trans_eq hdist

end

end RieszRectifiability

end OAI
