import OAI.Geometry.EinsteinFour.JacobiSchemeMatrix

namespace OAI

/-! The exact normalized coefficient in a discrete Jacobi pivot. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def relativeDiscretePosition (R : ℕ → NormalMatrix) (h : ℝ) (i : ℕ) : NormalMatrix :=
  if i = 0 then 1 else ((i : ℝ) * h)⁻¹ • discretePosition R h i

@[simp] theorem relativeDiscretePosition_zero (R : ℕ → NormalMatrix) (h : ℝ) :
    relativeDiscretePosition R h 0 = 1 := by simp [relativeDiscretePosition]

theorem relativeDiscretePosition_pos (R : ℕ → NormalMatrix) (h : ℝ) {i : ℕ}
    (hi : 0 < i) : relativeDiscretePosition R h i =
      ((i : ℝ) * h)⁻¹ • discretePosition R h i := by
  simp only [relativeDiscretePosition, ite_eq_right hi.ne']

theorem matrix_inverse_divided_time (s : ℝ) (hs : s ≠ 0) (X : NormalMatrix)
    (hX : IsUnit X.det) : (s⁻¹ • X)⁻¹ = s • X⁻¹ := by
  let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  rw [Matrix.inv_smul X s⁻¹ hX, invOf_eq_inv, inv_inv]

/-- Rescaling the discrete solution does not change any pivot ratio. -/
theorem normalizedDiscrete_ratio (R : ℕ → NormalMatrix) {h : ℝ} (hh : h ≠ 0)
    (i : ℕ) (hX : IsUnit (discretePosition R h i).det) :
    normalizedDiscrete R h (i + 1) * (normalizedDiscrete R h i)⁻¹ =
      discretePosition R h (i + 1) * (discretePosition R h i)⁻¹ := by
  simp only [normalizedDiscrete, matrix_inverse_divided_time h hh _ hX,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hh, one_smul]

/-- The pivot is `1 + P/i`, with `P` the discrete velocity times the
inverse of position divided by time. This identity explains the uniform
near-zero positivity criterion without introducing a time cutoff. -/
theorem discretePosition_ratio (R : ℕ → NormalMatrix) {h : ℝ} (hh : h ≠ 0)
    {i : ℕ} (hi : 0 < i) (hX : IsUnit (discretePosition R h i).det) :
    discretePosition R h (i + 1) * (discretePosition R h i)⁻¹ =
      1 + ((1 : ℝ) / i) • (discreteVelocity R h (i + 1) *
        (relativeDiscretePosition R h i)⁻¹) := by
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  rw [relativeDiscretePosition_pos R h hi,
    matrix_inverse_divided_time _ (mul_ne_zero hi' hh) _ hX,
    discretePosition_succ, add_mul, Matrix.mul_nonsing_inv _ hX]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  congr 1
  field_simp

end

end PositiveEinsteinFour.Jacobi

end OAI
