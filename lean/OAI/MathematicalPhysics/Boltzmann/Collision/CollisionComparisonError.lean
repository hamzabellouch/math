import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicCharacteristicGainUnit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicCharacteristicGainUnit
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1VelocityTranslationApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalFrequencyWindow

namespace OAI

/-! # The four physical errors in positive characteristic comparison -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def collisionComparisonError (N M : ℝ) (F H : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  |(gain N F p-gain M H p)/(1+F p+H p)|+
  |(lossDensity F p-loss N F p)/(1+F p)|+
  |(lossDensity H p-loss M H p)/(1+H p)|+
  |kineticFrequency F p-kineticFrequency H p|

theorem collisionComparisonError_measurable {N M : ℝ} {F H : X × Velocity → ℝ}
    (hF : Measurable F) (hH : Measurable H) : Measurable (collisionComparisonError N M F H) := by
  exact (((((gain_measurable N hF).sub (gain_measurable M hH)).div
    ((measurable_const.add hF).add hH)).abs.add
      (((lossDensity_measurable hF).sub (loss_measurable N hF)).div (measurable_const.add hF)).abs).add
      (((lossDensity_measurable hH).sub (loss_measurable M hH)).div (measurable_const.add hH)).abs).add
      ((kineticFrequency_measurable hF).sub (kineticFrequency_measurable hH)).abs

theorem collisionComparisonError_nonneg (N M : ℝ) (F H : X × Velocity → ℝ) (p : X × Velocity) :
    0 ≤ collisionComparisonError N M F H p := by
  unfold collisionComparisonError
  positivity

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
