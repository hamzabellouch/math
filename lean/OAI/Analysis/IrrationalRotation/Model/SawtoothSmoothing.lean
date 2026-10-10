import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

def smoothSawtooth (δ u : ℝ) : ℝ :=
  (2 * δ)⁻¹ * ∫ t in -δ..δ, Int.fract (u + t)

def smoothedDrop (C α δ u : ℝ) : ℝ :=
  C * (α + smoothSawtooth δ u - smoothSawtooth δ (u + α))

def smoothingTransfer (C δ u : ℝ) : ℝ :=
  C * (smoothSawtooth δ u - Int.fract u)

end InvariantProjection.Continuity

end

end OAI
