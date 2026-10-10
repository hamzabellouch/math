import OAI.MathematicalPhysics.Boltzmann.Branching.ConditionalMain
import OAI.MathematicalPhysics.Boltzmann.Branching.WeakCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.VelocityAveraging
import OAI.MathematicalPhysics.Boltzmann.Collision.CarlemanIdentity
import OAI.MathematicalPhysics.Boltzmann.Collision.MityaginDischarge

namespace OAI

section

/-! # Nonuniqueness from collision, compactness, and periodic existence hypotheses -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_analytic_input
    (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    (hDPhot : Published.DunfordPettis1940HotWindows)
    (hDPpair : Published.DunfordPettis1940HotPairWindows)
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement :=
  nonuniqueness_conditional hcarleman hGLPS hDP hDPhot hDPpair
    Published.mityagin2020FiveGainParameters hperiodic

end BoltzmannNonuniqueness


end

section

/-! # Nonuniqueness from the Carleman identity, averaging, and periodic existence -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_compactness_inputs
    (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3)
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement :=
  nonuniqueness_without_analytic_input hcarleman hGLPS
    Published.dunfordPettis1940Theorem321 Published.dunfordPettis1940HotWindows
    Published.dunfordPettis1940HotPairWindows hperiodic

end BoltzmannNonuniqueness


end

section

/-! # Nonuniqueness from averaging and periodic existence -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_carleman_input
    (hGLPS : Published.GLPS1988Proposition3)
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement :=
  nonuniqueness_without_compactness_inputs Published.gpv2009CarlemanInput hGLPS hperiodic

end BoltzmannNonuniqueness


end

section

/-! # Nonuniqueness assuming periodic global existence -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_averaging_input
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement :=
  nonuniqueness_without_carleman_input Published.glps1988Proposition3 hperiodic

end BoltzmannNonuniqueness


end

end OAI
