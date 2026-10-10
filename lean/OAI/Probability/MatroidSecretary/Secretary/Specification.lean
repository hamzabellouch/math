import OAI.Probability.MatroidSecretary.Secretary.ProbabilityModel
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Independent specification of the full-seed secretary endpoint

The rule and its finite initial seed law are chosen before the fixed vector
of weights and before the probability space or adversary.  The initial
uniform order is independent of the complete seed.  Only its ordered prefix
is preserved in the actual execution; the suffix may depend on all available
information, and even on additional randomization carried by the ambient
space.  No independence assumption is made on the executed order.

Finite seed types suffice for the manuscript construction: all conditional
reconstruction tables can be sampled in advance.  `Fin q` is just an
enumeration of this finite seed space, with its arbitrary probability law.
-/
