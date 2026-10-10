import Mathlib

namespace OAI

/-! The noncommuting resolvent identities in the quadratic cavity tilt.
These finite matrix statements include the zero-dimensional convention. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityResolvent {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - B * K)⁻¹ * B

private lemma cavity_inverse_pushThrough {d : ℕ} (C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - C * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * C = C * R := by
  calc
    J * C = J * C * ((1 - K * C) * R) := by rw [hR, mul_one]
    _ = (J * (1 - C * K)) * C * R := by noncomm_ring
    _ = C * R := by rw [hJ, one_mul]

private lemma cavity_inverse_difference {d : ℕ}
    (B C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - B * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * B - C * R = J * (B - C) * R := by
  calc
    J * B - C * R = J * B * ((1 - K * C) * R) - (J * (1 - B * K)) * C * R := by
      rw [hR, hJ, mul_one, one_mul]
    _ = J * (B - C) * R := by noncomm_ring

lemma cavityResolvent_pushThrough {d : ℕ} (K C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K C = C * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  exact cavity_inverse_pushThrough C K _ _
    (Matrix.nonsing_inv_mul _ hC) (Matrix.mul_nonsing_inv _ hR)

/-- Equation `cav:q-resolvent-difference`, with the matrix factors in their
required order. No commutation hypothesis is used. -/
theorem cavityResolvent_difference {d : ℕ} (K B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : IsUnit (1 - B * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K B - cavityResolvent K C =
      (1 - B * K)⁻¹ * (B - C) * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  rw [cavityResolvent_pushThrough K C hC]
  exact cavity_inverse_difference B C K _ _
    (Matrix.nonsing_inv_mul _ hB) (Matrix.mul_nonsing_inv _ hR)

theorem cavityResolvent_difference_symmetric {d : ℕ}
    (K B C : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hC : C.transpose = C)
    (hBdet : IsUnit (1 - B * K).det) (hCdet : IsUnit (1 - C * K).det) :
    cavityResolvent K B - cavityResolvent K C =
      (1 - B * K)⁻¹ * (B - C) * ((1 - C * K)⁻¹).transpose := by
  rw [cavityResolvent_difference K B C hBdet hCdet]
  congr 1
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hK, hC]

/-- The quadratic tilt replaces the original spectral block by the full
block in its resolvent, exactly as in `cav:q-transform`. -/
theorem cavityResolvent_spectral_transform {d : ℕ}
    (A A0 : Matrix (Fin d) (Fin d) ℝ) (b : ℝ)
    (h0 : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0).det)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det) :
    cavityResolvent (A - A0) ((b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0)⁻¹) =
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A)⁻¹ := by
  let D0 := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  have hD0 : IsUnit D0.det := h0
  have hD : IsUnit D.det := hA
  have hd : D = D0 - (A - A0) := by dsimp only [D, D0]; abel
  have hf : 1 - D0⁻¹ * (A - A0) = D0⁻¹ * D := by
    rw [hd]
    calc
      _ = D0⁻¹ * D0 - D0⁻¹ * (A - A0) := by rw [Matrix.nonsing_inv_mul D0 hD0]
      _ = _ := (mul_sub D0⁻¹ D0 (A - A0)).symm
  have hi : (1 - D0⁻¹ * (A - A0))⁻¹ = D⁻¹ * D0 := by
    apply Matrix.inv_eq_right_inv
    rw [hf]
    calc
      (D0⁻¹ * D) * (D⁻¹ * D0) = D0⁻¹ * (D * D⁻¹) * D0 := by simp only [mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv D hD, mul_one, Matrix.nonsing_inv_mul D0 hD0]
  change (1 - D0⁻¹ * (A - A0))⁻¹ * D0⁻¹ = D⁻¹
  rw [hi, mul_assoc, Matrix.mul_nonsing_inv D0 hD0, mul_one]

end InvariantIsing

end

end OAI
