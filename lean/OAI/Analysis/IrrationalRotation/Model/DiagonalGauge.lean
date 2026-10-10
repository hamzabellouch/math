import OAI.Analysis.IrrationalRotation.Model.WeightedShift
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.DiagonalGauge

abbrev Circle := AddCircle (1 : ℝ)
abbrev Fiber := WeightedShift.Hilbert

def weight (t : Circle) : WeightedShift.Weight :=
  ⟨fun k => fourier k t, memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    exact (Circle.norm_coe _).le⟩

def fiberOperator (t : Circle) : Fiber →L[ℂ] Fiber :=
  WeightedShift.diagonal (weight t)

def fieldOperator {X : Type*} [MeasurableSpace X] (μ : Measure X) (t : Circle) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  (fiberOperator t).compLpL 2 μ

def conjugate {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (t : Circle) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  fieldOperator μ t * A * fieldOperator μ (-t)

end Invariant233.DiagonalGauge

end

end OAI
