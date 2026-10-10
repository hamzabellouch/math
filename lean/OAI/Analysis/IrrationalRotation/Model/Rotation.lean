import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Model.WeightedShift
import OAI.Analysis.IrrationalRotation.Model.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.Rotation

instance circleMeasure_probability : IsProbabilityMeasure circleMeasure := by
  constructor
  change volume (Set.univ : Set Circle) = 1
  exact UnitAddCircle.measure_univ

abbrev Fiber := WeightedShift.Hilbert
abbrev Hilbert := MeasureTheory.Lp Fiber 2 circleMeasure

def action (θ : ℝ) (k : ℤ) (x : Circle) : Circle :=
  x + k • (θ : Circle)

def U : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure

def orbitWeight (θ : ℝ) (a : C(Circle, ℂ)) (x : Circle) : WeightedShift.Weight :=
  ⟨fun k => a (action θ k x), memℓp_infty <| by
    refine ⟨‖a‖, ?_⟩
    rintro r ⟨k, rfl⟩
    exact a.norm_coe_le_norm _⟩

def character : C(Circle, ℂ) := fourier 1

def representation (θ : ℝ) (a : C(Circle, ℂ)) : Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
    (fun k => by
      let : T0Space ℝ := @MetricSpace.instT0Space ℝ Real.metricSpace
      let : T0Space ℂ := @MetricSpace.instT0Space ℂ Complex.instNormedAddCommGroup.toMetricSpace
      change AEStronglyMeasurable (fun x : Circle => a (x + k • (θ : Circle))) circleMeasure
      exact (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)

def V (θ : ℝ) : Hilbert →L[ℂ] Hilbert := representation θ character

def algebra (θ : ℝ) : VonNeumannAlgebra Hilbert :=
  vonNeumannGenerated ({U, V θ} : Set (Hilbert →L[ℂ] Hilbert))

def weighted (θ : ℝ) (a : C(Circle, ℂ)) : Hilbert →L[ℂ] Hilbert :=
  U * representation θ a

def complexWeight (f : C(Circle, ℝ)) : C(Circle, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

def weightedReal (θ : ℝ) (f : C(Circle, ℝ)) : Hilbert →L[ℂ] Hilbert :=
  weighted θ (complexWeight f)

def vacuum : Hilbert := Lp.const 2 circleMeasure (lp.single 2 (0 : ℤ) (1 : ℂ))

def vacuumFunctional (T : Hilbert →L[ℂ] Hilbert) : ℂ := inner ℂ vacuum (T vacuum)

end Invariant233.Rotation

end

end OAI
