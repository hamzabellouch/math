import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def NormalAlexandrovContact (v : M → ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x)
    (A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) : Prop :=
  p∈activeLogs (n := n) v x ∧ p∈injectivityDomain x ∧
  (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
  HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A
end WeakMTWTransport

end

end OAI
