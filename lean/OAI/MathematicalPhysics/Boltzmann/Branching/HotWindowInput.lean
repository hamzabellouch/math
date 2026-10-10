import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

/-! # The published weak compactness input on local blow-up windows

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Trans. AMS 47 (1940), Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.

Sequential weak compactness applies on bounded time and spatial windows
in the nonperiodic dilation coordinates. Uniform integrability includes the common
L¹ bound, and uniform tightness controls the unbounded velocity variable.
The input does not assert compatibility of the local limits, a transport
equation, velocity averaging, or any nonlinear limit identification.
-/

noncomputable section

namespace BoltzmannNonuniqueness.Published

def DunfordPettis1940HotWindows : Prop :=
  ∀ A R : ℝ, 0 ≤ A → 0 ≤ R →
    L1WeakCompactnessInput (JetCopyDatum.AttainedCapSequence.hotWindowVolume A R)

end BoltzmannNonuniqueness.Published

end

end OAI
