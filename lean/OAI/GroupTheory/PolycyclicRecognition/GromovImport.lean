import OAI.GroupTheory.PolycyclicRecognition.Algebra.GromovGrowthBridge
import Gromov.FormalConjecturesCheck

namespace OAI

/-! # Gromov’s polynomial-growth theorem in arbitrary universes. -/
namespace PolycyclicRecognition
universe u
variable {J : Type u} [Group J] [DecidableEq J]

/-- Polynomial word growth implies virtual nilpotence in every universe. -/
theorem gromovPolynomialGrowthInput : GromovPolynomialGrowthInput J := by
  intro T hT hgen hgrowth
  exact FormalConjecturesCheck.gromov_forward J
    (hasPolynomialGrowth_of_wordBall T hT hgen hgrowth)

end PolycyclicRecognition

end OAI
