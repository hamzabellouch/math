import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Probability-space topology for fusion.

A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156 (1995),
Theorems 17.23 and 17.24, pp. 112–113, give the Polish weak topology
on probability laws on a Polish space and identify its Borel sigma algebra
with the evaluation sigma algebra. The following paragraph gives the
standard Borel consequence.
-/

open MeasureTheory

namespace CircleDomainRigidity

def StandardBorelProbabilityLaws (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  StandardBorelSpace (ProbabilityMeasure Ω)

def PolishProbabilityLaws (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] : Prop :=
  PolishSpace (ProbabilityMeasure Ω) ∧ BorelSpace (ProbabilityMeasure Ω)

end CircleDomainRigidity

end OAI
