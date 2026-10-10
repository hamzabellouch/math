import OAI.Probability.InvariantIsing.Cavity.CavityResolvent

namespace OAI

/-! The finite-dimensional algebra in `cav:q-factor` and the backward
quadratic recursion.  The factors retain their order: neither the two
covariances nor the quadratic coefficient need commute. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

/-- The coefficient `K_i = K (1 - H_i K)⁻¹` of the backward quadratic. -/
def cavityBackwardQuadratic {d : ℕ} (K H : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := K * (1 - H * K)⁻¹

/-- The conditional-mean matrix at a step from covariance `P` to `C`. -/
def cavityStepTransition {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := (1 - (P - C) * cavityBackwardQuadratic K C)⁻¹

theorem cavity_quadratic_factor {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    1 - (P - C) * cavityBackwardQuadratic K C =
      (1 - P * K) * (1 - C * K)⁻¹ := by
  unfold cavityBackwardQuadratic
  calc
    1 - (P - C) * (K * (1 - C * K)⁻¹) =
        (1 - C * K) * (1 - C * K)⁻¹ -
          (P - C) * (K * (1 - C * K)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hC]
    _ = (1 - P * K) * (1 - C * K)⁻¹ := by noncomm_ring

theorem cavity_quadratic_det_ratio {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    (1 - (P - C) * cavityBackwardQuadratic K C).det =
      (1 - P * K).det / (1 - C * K).det := by
  apply (eq_div_iff hC.ne_zero).2
  rw [cavity_quadratic_factor K P C hC, Matrix.det_mul]
  rw [mul_assoc, Matrix.det_nonsing_inv_mul_det _ hC, mul_one]

theorem cavity_quadratic_step_isUnit {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    IsUnit (1 - (P - C) * cavityBackwardQuadratic K C).det := by
  rw [cavity_quadratic_factor K P C hC, Matrix.det_mul]
  exact hP.mul (Matrix.isUnit_nonsing_inv_det _ hC)

theorem cavityStepTransition_eq {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityStepTransition K P C = (1 - C * K) * (1 - P * K)⁻¹ := by
  unfold cavityStepTransition
  apply Matrix.inv_eq_right_inv
  rw [cavity_quadratic_factor K P C hC]
  calc
    ((1 - P * K) * (1 - C * K)⁻¹) *
        ((1 - C * K) * (1 - P * K)⁻¹) =
        (1 - P * K) * ((1 - C * K)⁻¹ * (1 - C * K)) * (1 - P * K)⁻¹ := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ hC, mul_one, Matrix.mul_nonsing_inv _ hP]

/-- The identity `J_i T_i = J_{i-1}` used in square completion. -/
theorem cavity_quadratic_backward_inverse {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    (1 - C * K)⁻¹ * cavityStepTransition K P C = (1 - P * K)⁻¹ := by
  rw [cavityStepTransition_eq K P C hP hC, ← mul_assoc,
    Matrix.nonsing_inv_mul _ hC, one_mul]

/-- The backward coefficient after integrating one level is exactly
`K_{i-1}`; this is the matrix identity in `cav:q-gaussian-integral`. -/
theorem cavityBackwardQuadratic_step {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityBackwardQuadratic K C * cavityStepTransition K P C =
      cavityBackwardQuadratic K P := by
  unfold cavityBackwardQuadratic
  rw [mul_assoc, cavity_quadratic_backward_inverse K P C hP hC]

theorem cavityBackwardQuadratic_transpose {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.transpose = H)
    (hHdet : IsUnit (1 - H * K).det) :
    (cavityBackwardQuadratic K H).transpose = cavityBackwardQuadratic K H := by
  have hKH : IsUnit (1 - K * H).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  unfold cavityBackwardQuadratic
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hH, hK]
  exact cavityResolvent_pushThrough H K hKH

@[simp] theorem cavityBackwardQuadratic_zero {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) :
    cavityBackwardQuadratic K 0 = K := by
  simp [cavityBackwardQuadratic]

end InvariantIsing

end

end OAI
