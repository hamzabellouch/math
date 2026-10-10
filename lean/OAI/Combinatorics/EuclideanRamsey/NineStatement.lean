import OAI.Combinatorics.EuclideanRamsey.Nine

namespace OAI

/-! The literal rational parametrization of the nine-point circle configuration. -/

noncomputable section
namespace EuclideanRamsey.NineStatement

/-- The rational parametrization of nine points in the Euclidean plane. -/
def literalCircleConfig (t : Fin 9 → ℝ) (i : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![(1 - (t i)^2) / (1 + (t i)^2),
    (2 * t i) / (1 + (t i)^2)]

theorem literalCircleConfig_eq (t : Fin 9 → ℝ) :
    literalCircleConfig t = NineGeometry.circleConfig t := by
  funext i
  ext j
  fin_cases j <;>
    simp [literalCircleConfig, NineGeometry.circleConfig]

/-- Nine points on the unit circle form a non-Ramsey configuration when their
parameters are algebraically independent over the rationals. -/
theorem nine_circle_configuration (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (literalCircleConfig t) ∧
      (∀ i, dist (literalCircleConfig t i) 0 = 1) ∧
      ¬ Ramsey (literalCircleConfig t) := by
  rw [literalCircleConfig_eq]
  exact NineMain.nine_circle_configuration t ht

end EuclideanRamsey.NineStatement

end

end OAI
