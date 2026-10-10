import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.BiasedTailDensity

def tailDensity {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure P) (g : P × Z → ℝ) (z : Z) : ℝ :=
  ∫ u, g (u, z) ∂μ

end Invariant233.BiasedTailDensity

end

end OAI
