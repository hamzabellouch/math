import OAI.Analysis.IrrationalRotation.Model.ProductBase
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

def coordinateOrderFailure (θ : ℕ → ℝ) (n : ℕ) (i : ℕ) : Set Base :=
  {x | circleRepresentative (rotationIterate θ (n : ℤ) x i) <
    circleRepresentative (x i)}

def tailOrderFailure (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) : Set Base :=
  ⋃ i : {i : ℕ // i ∉ I}, coordinateOrderFailure θ n i

namespace TailTrimming

def orbitPairMap (θ : ℕ → ℝ) (n : ℕ) (x : Base) : Base × Base :=
  (x, rotationIterate θ (n : ℤ) x)

def orbitPairMeasure (θ : ℕ → ℝ) (n : ℕ) (w : Base → ℝ≥0∞) : Measure (Base × Base) :=
  (baseMeasure.withDensity w).map (orbitPairMap θ n)

def orbitAverageMeasure (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) : Measure (Base × Base) :=
  (N.card : ℝ≥0∞)⁻¹ • ∑ n ∈ N, orbitPairMeasure θ n (w n)

def orderedPairEvent : Set (Base × Base) := {xy | Ordered xy.1 xy.2}

end TailTrimming

end Invariant233.ProductModel

end

end OAI
