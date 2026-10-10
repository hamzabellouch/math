import OAI.Geometry.EinsteinFour.JacobiSchemeRatios

namespace OAI

/-! Symmetry of the discrete Jacobi ratios from their preserved Wronskian. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem kick_wronskian (X V A : NormalMatrix) (h : ℝ)
    (hA : Aᵀ = A) (hXV : Xᵀ * V = Vᵀ * X) :
    Xᵀ * (V - h • (A * X)) = (V - h • (A * X))ᵀ * X := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hA, hXV, Matrix.mul_assoc]

theorem drift_wronskian (X W : NormalMatrix) (h : ℝ)
    (hXW : Xᵀ * W = Wᵀ * X) :
    (X + h • W)ᵀ * W = Wᵀ * (X + h • W) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, add_mul, mul_add,
    mul_smul_comm, smul_mul_assoc, hXW]

theorem discrete_wronskian (R : ℕ → NormalMatrix) (h : ℝ)
    (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ) :
    (discretePosition R h i)ᵀ * discreteVelocity R h i =
      (discreteVelocity R h i)ᵀ * discretePosition R h i := by
  induction i with
  | zero => simp
  | succ i hi =>
      have hw := kick_wronskian (discretePosition R h i) (discreteVelocity R h i)
        (R i) h (hR i) hi
      rw [← discreteVelocity_succ] at hw
      simpa only [discretePosition_succ] using
        drift_wronskian (discretePosition R h i) (discreteVelocity R h (i + 1)) h hw

theorem next_discrete_wronskian (R : ℕ → NormalMatrix) (h : ℝ)
    (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ) :
    (discretePosition R h i)ᵀ * discreteVelocity R h (i + 1) =
      (discreteVelocity R h (i + 1))ᵀ * discretePosition R h i := by
  rw [discreteVelocity_succ]
  exact kick_wronskian _ _ _ _ (hR i) (discrete_wronskian R h hR i)

theorem ratio_symmetric_of_wronskian {X V : NormalMatrix}
    (hX : IsUnit X.det) (hXV : Xᵀ * V = Vᵀ * X) :
    (V * X⁻¹)ᵀ = V * X⁻¹ := by
  have hleft : X⁻¹ᵀ * Xᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hX, Matrix.transpose_one]
  have hh := congrArg (fun A : NormalMatrix => X⁻¹ᵀ * A * X⁻¹) hXV
  have hl : X⁻¹ᵀ * (Xᵀ * V) * X⁻¹ = V * X⁻¹ := by
    rw [← Matrix.mul_assoc X⁻¹ᵀ Xᵀ V, hleft, one_mul]
  have hr : X⁻¹ᵀ * (Vᵀ * X) * X⁻¹ = X⁻¹ᵀ * Vᵀ := by
    rw [Matrix.mul_assoc X⁻¹ᵀ, Matrix.mul_assoc Vᵀ, Matrix.mul_nonsing_inv _ hX,
      mul_one]
  rw [hl, hr] at hh
  rw [Matrix.transpose_mul]
  exact hh.symm

theorem discrete_ratio_symmetric (R : ℕ → NormalMatrix) (h : ℝ)
    (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ)
    (hX : IsUnit (discretePosition R h i).det) :
    (discretePosition R h (i + 1) * (discretePosition R h i)⁻¹)ᵀ =
      discretePosition R h (i + 1) * (discretePosition R h i)⁻¹ := by
  have hw := next_discrete_wronskian R h hR i
  have hv := ratio_symmetric_of_wronskian hX hw
  rw [discretePosition_succ, add_mul, Matrix.mul_nonsing_inv _ hX, smul_mul_assoc]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hv]

def pivotCoefficient (R : ℕ → NormalMatrix) (h : ℝ) (i : ℕ) : NormalMatrix :=
  discreteVelocity R h (i + 1) * (relativeDiscretePosition R h i)⁻¹

/-- Symmetry also holds for the totalized coefficient before the mesh is
known to be preconjugate: a singular position has inverse zero. -/
theorem one_add_pivotCoefficient_symmetric (R : ℕ → NormalMatrix) {h : ℝ}
    (hh : h ≠ 0) (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ) :
    ((1 : NormalMatrix) + ((1 : ℝ) / i) • pivotCoefficient R h i)ᵀ =
      1 + ((1 : ℝ) / i) • pivotCoefficient R h i := by
  by_cases hi : i = 0
  · subst i
    simp
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    by_cases hX : IsUnit (discretePosition R h i).det
    · rw [pivotCoefficient, ← discretePosition_ratio R hh hip hX]
      exact discrete_ratio_symmetric R h hR i hX
    · have hx0 : (discretePosition R h i).det = 0 := by
        simpa only [isUnit_iff_ne_zero, not_not] using hX
      have hb0 : (relativeDiscretePosition R h i).det = 0 := by
        rw [relativeDiscretePosition_pos R h hip, Matrix.det_smul, hx0, mul_zero]
      have hb : ¬IsUnit (relativeDiscretePosition R h i).det := by simp [hb0]
      simp only [pivotCoefficient, Matrix.nonsing_inv_apply_not_isUnit _ hb,
        mul_zero, smul_zero, add_zero, Matrix.transpose_one]

end

end PositiveEinsteinFour.Jacobi

end OAI
