import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace RuledApproximation

def OrthogonalZeroDiagonalStatement : Prop :=
  ∀ A : Plane →L[ℝ] Plane, LinearMap.trace ℝ Plane A.toLinearMap = 0 →
    LinearMap.det A.toLinearMap < 0 →
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ b c : ℝ,
      (∀ z : Plane, R.symm (A (R z)) = vec2 (b * z 1) (c * z 0)) ∧
      b * c = -LinearMap.det A.toLinearMap ∧ 0 < b * c ∧
      |b| ≤ ‖A‖ ∧ |c| ≤ ‖A‖

end RuledApproximation

end

end OAI
