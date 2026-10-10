import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.Shells
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierPolynomialSmoothing

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def complexOfPositive (μ : FiniteMeasure ℝ) : ComplexMeasure ℝ :=
  (μ : Measure ℝ).toSignedMeasure.toComplexMeasure 0

noncomputable def complexFourier (ν : ComplexMeasure ℝ) (r : ℝ) : ℂ :=
  VectorMeasure.integral ν (fun x : ℝ => Complex.exp (-((r:ℂ)*(x:ℂ)*Complex.I)))
    (ContinuousLinearMap.mul ℝ ℂ)
noncomputable def complexShellEnergy (ν : ComplexMeasure ℝ) (N : ℕ) : ℝ :=
  ∫ r in PlanarFalconer.dyadicShell N, ‖complexFourier ν r‖^2

noncomputable def complexVariationError (μ : FiniteMeasure ℝ) (ν : ComplexMeasure ℝ) : ℝ :=
  (complexOfPositive μ - ν).variation.real univ
end CurrentFalconer.MonotoneShell
end
end

end OAI
