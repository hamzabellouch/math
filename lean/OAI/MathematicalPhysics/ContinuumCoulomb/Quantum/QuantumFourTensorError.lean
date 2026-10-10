import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorForms

namespace OAI

/-! The counterterm's off-diagonal contribution to the second-order energy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem qmaInverse_symmetric (A T : H →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x)
    (hA : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ) (x y : H) :
    ⟪x,T y⟫_ℝ = ⟪T x,y⟫_ℝ := by
  calc
    _ = ⟪A (T x),T y⟫_ℝ := by rw [hAT]
    _ = ⟪T x,A (T y)⟫_ℝ := (hA _ _).symm
    _ = _ := by rw [hAT]

theorem qmaSecondOrder_column_identity (T : H →L[ℝ] H) {r : ℝ} (hr : r ≠ 0)
    (hT : ∀ x y, ⟪x,T y⟫_ℝ = ⟪T x,y⟫_ℝ) (w z : H)
    (hw : T w = (8*r^2)⁻¹ • w) :
    ⟪r • w+z,T (r • w+z)⟫_ℝ-(1/8)*‖w‖^2 =
      (1/(4*r))*⟪w,z⟫_ℝ+⟪z,T z⟫_ℝ := by
  have hwz : ⟪w,T z⟫_ℝ = (8*r^2)⁻¹*⟪w,z⟫_ℝ := by
    rw [hT,hw,inner_smul_left]
    simp only [starRingEnd_apply,star_trivial]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    starRingEnd_apply,star_trivial,hwz,hw,real_inner_self_eq_norm_sq]
  simp only [real_inner_comm z w]
  field_simp
  ring

theorem qmaSecondOrder_column_error (T : H →L[ℝ] H) {r v c l : ℝ} (hr : 0 < r)
    (hv : 0 ≤ v) (_hc : 0 ≤ c) (hl : 0 ≤ l)
    (hT : ∀ x y, ⟪x,T y⟫_ℝ = ⟪T x,y⟫_ℝ) (hTn : ‖T‖ ≤ 1/(4*r^2))
    (w z : H) (hw : T w = (8*r^2)⁻¹ • w) (hwn : ‖w‖ ≤ v*l) (hzn : ‖z‖ ≤ c*l) :
    |⟪r • w+z,T (r • w+z)⟫_ℝ-(1/8)*‖w‖^2| ≤
      (v*c/(4*r)+c^2/(4*r^2))*l^2 := by
  have hwz : |⟪w,z⟫_ℝ| ≤ v*c*l^2 := by
    calc
      _ ≤ ‖w‖*‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ (v*l)*(c*l) := mul_le_mul hwn hzn (norm_nonneg _) (mul_nonneg hv hl)
      _ = _ := by ring
  have hz2 : ‖z‖^2 ≤ c^2*l^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg z) hzn 2
  have hzt : |⟪z,T z⟫_ℝ| ≤ c^2/(4*r^2)*l^2 := by
    calc
      _ ≤ ‖z‖*‖T z‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖z‖*(‖T‖*‖z‖) := mul_le_mul_of_nonneg_left (T.le_opNorm z) (norm_nonneg z)
      _ = ‖T‖*‖z‖^2 := by ring
      _ ≤ (1/(4*r^2))*(c^2*l^2) := mul_le_mul hTn hz2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  rw [qmaSecondOrder_column_identity T (ne_of_gt hr) hT w z hw]
  calc
    _ ≤ |(1/(4*r))*⟪w,z⟫_ℝ|+|⟪z,T z⟫_ℝ| := abs_add_le _ _
    _ = (1/(4*r))*|⟪w,z⟫_ℝ|+|⟪z,T z⟫_ℝ| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(4*r))]
    _ ≤ (1/(4*r))*(v*c*l^2)+c^2/(4*r^2)*l^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hwz (by positivity)) hzt
    _ = _ := by ring

theorem qmaSecondOrder_inverse_column_bound (T : H →L[ℝ] H) {r v c l : ℝ} (hr : 0 < r)
    (hTn : ‖T‖ ≤ 1/(4*r^2)) (w z : H) (hw : T w = (8*r^2)⁻¹ • w)
    (hwn : ‖w‖ ≤ v*l) (hzn : ‖z‖ ≤ c*l) :
    ‖T (r • w+z)‖ ≤ (v/(8*r)+c/(4*r^2))*l := by
  rw [map_add,map_smul,hw,smul_smul]
  have hs : r*(8*r^2)⁻¹ = 1/(8*r) := by field_simp
  rw [hs]
  calc
    _ ≤ ‖(1/(8*r)) • w‖+‖T z‖ := norm_add_le _ _
    _ = (1/(8*r))*‖w‖+‖T z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    _ ≤ (1/(8*r))*(v*l)+(1/(4*r^2))*(c*l) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hwn (by positivity))
      exact (T.le_opNorm z).trans
        (mul_le_mul hTn hzn (norm_nonneg _) (by positivity))
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
