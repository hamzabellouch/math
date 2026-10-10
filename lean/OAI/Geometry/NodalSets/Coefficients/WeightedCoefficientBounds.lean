import Mathlib.Tactic.FieldSimp
import OAI.Geometry.NodalSets.Elliptic.IndependentWeightedMatrix
import OAI.Geometry.NodalSets.Elliptic.PositiveMatrixBounds

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma weightedBaseMatrix_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b r R rho : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hrho : r ≤ rho) (hR : rho ≤ R)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) (v : n → ℝ) :
    (r/b) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (weightedBaseMatrix A rho *ᵥ v) ∧
    v ⬝ᵥ (weightedBaseMatrix A rho *ᵥ v) ≤ (R/a) * (v ⬝ᵥ v) := by
  have h := positive_matrix_inverse_bounds A hA a b ha hb hlo hhi v
  have hv := real_dot_self_nonneg v
  have hi : 0 ≤ v ⬝ᵥ (A⁻¹ *ᵥ v) := le_trans (by positivity) h.1
  simp only [weightedBaseMatrix, smul_mulVec, dotProduct_smul, smul_eq_mul]
  constructor
  · calc
      _ = r * (b⁻¹ * (v ⬝ᵥ v)) := by ring
      _ ≤ r * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := mul_le_mul_of_nonneg_left h.1 hr.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hrho hi
  · calc
      _ ≤ R * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := mul_le_mul_of_nonneg_right hR hi
      _ ≤ R * (a⁻¹ * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left h.2 ((hr.trans_le hrho).trans_le hR).le
      _ = _ := by ring

lemma determinant_density_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b r R rho : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hrho : r ≤ rho) (hR : rho ≤ R)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) :
    a ^ Fintype.card n / R^2 ≤ (Real.sqrt A.det / rho)^2 ∧
    (Real.sqrt A.det / rho)^2 ≤ b ^ Fintype.card n / r^2 := by
  have h := positive_matrix_determinant_bounds A hA a b ha.le hlo hhi
  have hrp : 0 < rho := hr.trans_le hrho
  have hRp : 0 < R := hrp.trans_le hR
  rw [div_pow, Real.sq_sqrt hA.det_pos.le]
  constructor
  · exact div_le_div₀ hA.det_pos.le h.1 (sq_pos_of_pos hrp) (by nlinarith)
  · exact div_le_div₀ (pow_nonneg hb.le _) h.2 (sq_pos_of_pos hr) (by nlinarith)

end
end Yau.Geometry

end OAI
