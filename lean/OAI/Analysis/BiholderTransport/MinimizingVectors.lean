import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

def minimizingVectors (x : M) : Set (TangentSpace 𝓘(ℝ, Model n) x) :=
  {p | dist x (riemannianExp x p) = ‖p‖}

end WeakMTWTransport
end

end OAI
