import OAI.MathematicalPhysics.Boltzmann.Branching.PeriodicExistenceReduction
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicExistenceDischarge

namespace OAI

/-! # Global nonuniqueness via periodic continuation -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_proved : NonuniquenessStatement :=
  nonuniqueness_without_averaging_input periodicExistenceInput

end BoltzmannNonuniqueness

end OAI
