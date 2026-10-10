import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Model.ScalarSampling

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel.IdealSampling

def endpoint (I D : Finset ℕ) (h : ℝ) (x z : Base) : Base :=
  fun i => if i ∈ I then z i else if i ∈ D then
    x i + ((h * ScalarSampling.delta (circleRepresentative (x i)) *
      circleRepresentative (z i) : ℝ) : Circle) else x i

def endpointMap (I D : Finset ℕ) (h : ℝ) (xz : EndpointPair) : EndpointPair :=
  (xz.1, endpoint I D h xz.1 xz.2)

def cutoffEvent (I D : Finset ℕ) (α : ℝ) : Set EndpointPair :=
  {xz | ∀ i ∈ D \ I, α ≤ ScalarSampling.delta (circleRepresentative (xz.1 i))}

def sourceMeasure (I : Finset ℕ) : Measure EndpointPair :=
  (baseMeasure.prod baseMeasure).restrict (triangularEvent I)

def uncutLaw (I D : Finset ℕ) (h : ℝ) : Measure EndpointPair :=
  (sourceMeasure I).map (endpointMap I D h)

def law (I D : Finset ℕ) (h α : ℝ) : Measure EndpointPair :=
  ((sourceMeasure I).restrict (cutoffEvent I D α)).map (endpointMap I D h)

end Invariant233.ProductModel.IdealSampling

end

end OAI
