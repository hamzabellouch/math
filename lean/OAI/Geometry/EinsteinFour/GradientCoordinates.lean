import OAI.Geometry.EinsteinFour.GradientCoordinateModel

namespace OAI

/-! Quadratic compression in the fixed Bianchi coordinate model. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Direct quadratic compression on actual Bianchi tensors. -/
theorem generator_row_energy (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ a, ∑ b, ‖rawGradientGenerator s Z.matrix a b‖ ^ 2) +
      40 * (∑ b, ‖Z.matrix s b‖ ^ 2) = 25 * Z.squaredNorm := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [generator_coordinates]
  change (costParameters (generatorCoordinates s v)).squaredNorm +
    40 * (∑ b, ‖(costParameters v).matrix s b‖ ^ 2) = 25 * (costParameters v).squaredNorm
  rw [costParameters_norm, costParameters_norm]
  fin_cases s <;> dsimp only
  · change coordinateNorm (generatorCoordinates 0 v) +
      40 * (∑ b, ‖(costParameters v).matrix 0 b‖ ^ 2) = 25 * coordinateNorm v
    rw [generator_norm_0, row_norm_0]
    unfold coordinateNorm
    ring
  · change coordinateNorm (generatorCoordinates 1 v) +
      40 * (∑ b, ‖(costParameters v).matrix 1 b‖ ^ 2) = 25 * coordinateNorm v
    rw [generator_norm_1, row_norm_1]
    unfold coordinateNorm
    ring
  · change coordinateNorm (generatorCoordinates 2 v) +
      40 * (∑ b, ‖(costParameters v).matrix 2 b‖ ^ 2) = 25 * coordinateNorm v
    rw [generator_norm_2, row_norm_2]
    unfold coordinateNorm
    ring

/-- Contracting the actual generators gives the diagonal matrix-slot form. -/
theorem weighted_generator_matrixForm (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    -(∑ s, t s * (∑ a, ∑ b, ‖rawGradientGenerator s Z.matrix a b‖ ^ 2)) / 40 =
      ∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2) := by
  have h0 := congrArg (fun x : ℝ => t 0 * x) (generator_row_energy 0 Z hz hb)
  have h1 := congrArg (fun x : ℝ => t 1 * x) (generator_row_energy 1 Z hz hb)
  have h2 := congrArg (fun x : ℝ => t 2 * x) (generator_row_energy 2 Z hz hb)
  have htrace := congrArg (fun x : ℝ => 25 * x * Z.squaredNorm) ht
  simp only [Fin.sum_univ_three] at h0 h1 h2 htrace ⊢
  linear_combination (-1 / 40 : ℝ) * h0 + (-1 / 40 : ℝ) * h1 +
    (-1 / 40 : ℝ) * h2 + (-1 / 40 : ℝ) * htrace

end
end PositiveEinsteinFour.Bianchi

end OAI
