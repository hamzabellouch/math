import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.DirectIntegral

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure Ω}

def shiftedPullback (S : E →L[ℂ] E) (σ : Ω → Ω)
    (hσ : MeasurePreserving σ μ μ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (S.compLpL 2 μ).comp (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).toContinuousLinearMap

end Invariant233.DirectIntegral

end

end OAI
