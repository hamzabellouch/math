import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteLimit

namespace OAI

/-! Parameter perturbations of the actual fixed-power finite exterior equation. -/

namespace DefocusingNLS

theorem radialExteriorFiniteField_parameter_difference (ν μ : ℂ) (n : ℕ)
    (m : ℝ → ℂ) (δ t : ℝ) (z : ℂ × ℂ) :
    ‖radialExteriorFiniteField ν n m δ t z-radialExteriorFiniteField μ n m δ t z‖ ≤
      radialExteriorMatrixDifference ν μ*‖z‖ := by
  have he : radialExteriorFiniteField ν n m δ t z-radialExteriorFiniteField μ n m δ t z =
      radialExteriorErrorMatrix ν z-radialExteriorErrorMatrix μ z := by
    unfold radialExteriorFiniteField
    abel
  rw [he]
  exact radialExteriorErrorMatrix_difference ν μ z

end DefocusingNLS

end OAI
