import OAI.GroupTheory.Thompson.UnitBall
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

noncomputable section

namespace ThompsonNonamenability.Analytic

open MeasureTheory Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev intervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

abbrev Hilbert := Lp Plane 2 intervalMeasure

abbrev Ball := UnitBall Hilbert

end ThompsonNonamenability.Analytic

end

end OAI
