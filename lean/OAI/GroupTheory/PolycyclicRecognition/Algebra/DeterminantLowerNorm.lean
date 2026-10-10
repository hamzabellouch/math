import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Quantitative invertibility from a determinant lower bound

Compactness bounds the adjugate on the unit ball. Homogeneity then gives
the polynomial loss needed to choose injective patches for polynomial maps.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric Matrix
open scoped Matrix.Norms.Operator

theorem exists_adjugate_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Matrix (Fin n) (Fin n) ℝ) (L : ℝ),
      0 < L → ‖A‖ ≤ L → ‖A.adjugate‖ ≤ C * L ^ (n - 1) := by
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) :=
    continuous_id.matrix_adjugate
  obtain ⟨C, hC, hbound⟩ := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1).image hc
    |>.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun A L hL hA => ?_⟩
  have hunit : L⁻¹ • A ∈ closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact (inv_mul_le_iff₀ hL).mpr (by simpa using hA)
  have h := hbound _ ⟨L⁻¹ • A, hunit, rfl⟩
  dsimp only at h
  rw [Matrix.adjugate_smul, Fintype.card_fin, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (inv_pos.mpr hL) _), inv_pow] at h
  have he := (inv_mul_le_iff₀ (pow_pos hL (n - 1))).mp h
  simpa only [mul_comm] using he

/-- The adjugate identity bounds below the action of the original matrix. -/
theorem determinant_mul_norm_le_adjugate_mul_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    |A.det| * ‖v‖ ≤ ‖A.adjugate‖ * ‖A *ᵥ v‖ := by
  have he : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hb := Matrix.linfty_opNorm_mulVec A.adjugate (A *ᵥ v)
  rw [he, norm_smul, Real.norm_eq_abs] at hb
  exact hb

/-- Uniform lower norm control for all matrices with bounded norm and a
prescribed positive determinant lower bound. -/
theorem exists_determinant_lower_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (L η : ℝ),
      0 < L → ‖A‖ ≤ L → η ≤ |A.det| → ∀ v,
      η * ‖v‖ ≤ (C * L ^ (n - 1)) * ‖A v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_adjugate_norm_bound n
  refine ⟨C, hC, fun A L η hL hA hη v => ?_⟩
  let M := LinearMap.toMatrix' A.toLinearMap
  have hM : ‖M‖ ≤ L := by simpa only [M, Matrix.linfty_opNorm_toMatrix] using hA
  have hb := determinant_mul_norm_le_adjugate_mul_norm M v
  dsimp only [M] at hb
  rw [LinearMap.det_toMatrix', LinearMap.toMatrix'_mulVec] at hb
  exact (mul_le_mul_of_nonneg_right hη (norm_nonneg v)).trans
    (hb.trans (mul_le_mul_of_nonneg_right (hbound M L hL hM) (norm_nonneg (A v))))

end PolycyclicRecognition

end

end OAI
