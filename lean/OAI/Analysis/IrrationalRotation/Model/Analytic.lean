import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

abbrev Circle := AddCircle (1 : ℝ)

def circleMeasure : Measure Circle := volume

def negLogCost (t : ℝ) : ℝ≥0∞ :=
  if t = 0 then ∞ else ENNReal.ofReal (-Real.log |t|)

def HasNegInfiniteLogIntegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : Prop :=
  (∫⁻ x, negLogCost (f x) ∂μ) = ∞

def scalarWeightDeterminant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  EReal.exp (-((∫⁻ x, negLogCost (f x) ∂μ) : EReal))

def NormQuasinilpotent {A : Type*} [NormedRing A] (T : A) : Prop :=
  Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)

def IsContinuousCircleWeight (f : Circle → ℝ) : Prop :=
  Continuous f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    (∀ x, f x = 0 ↔ x = 0) ∧ HasNegInfiniteLogIntegral circleMeasure f

end Invariant233

end

end OAI
