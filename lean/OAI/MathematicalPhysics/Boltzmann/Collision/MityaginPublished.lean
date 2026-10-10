import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainRank
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Published scalar analytic zero-set input

B. S. Mityagin, *The Zero Set of a Real Analytic Function*, Mathematical
Notes 107(3) (2020), 529–530, DOI 10.1134/S0001434620030189.
The author preprint arXiv:1512.07276, Proposition 0, states the corresponding
connected-open-domain zero-set theorem. Here it is specialized to the twenty
real coordinates of the five-gain parameter space, as a conditional
zero-set nullity statement.
-/

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Published

def Mityagin2020FiveGainParameters : Prop :=
  ∀ (U : Set FiveGainMap.Parameters), IsOpen U → IsPreconnected U →
    ∀ f : FiveGainMap.Parameters → ℝ, AnalyticOnNhd ℝ f U →
      (∃ q ∈ U, f q ≠ 0) → volume {q ∈ U | f q = 0} = 0

end BoltzmannNonuniqueness.Published

end OAI
