import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

/-- The radial shell measure shared by the planar and all-dimensional arguments. -/
noncomputable def sourceAngularShellMeasure (v : ℝ) (Ψ : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun r => ENNReal.ofReal (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v))

end PlanarFalconer

end OAI
