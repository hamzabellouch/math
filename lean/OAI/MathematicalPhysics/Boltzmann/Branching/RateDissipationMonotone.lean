import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation

namespace OAI

/-! # Monotonicity of the nonnegative dissipation in the base measure -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem rateDissipation_mono_measure {μ ν : Measure X} (h : μ ≤ ν)
    (f : X × Velocity → ℝ) : rateDissipation μ f ≤ rateDissipation ν f := by
  unfold rateDissipation
  gcongr

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
