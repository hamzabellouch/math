import Mathlib
import OAI.Geometry.WeakMTW.Model

namespace OAI

namespace WeakMTWGlobalSupport

section

open scoped Manifold ContDiff Topology
open Set Filter Manifold Bundle

namespace WeakMTW

noncomputable section

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

def minimizingDomain (x : M) : Set (TangentSpace (model n) x) :=
  {v | dist x (exp x v) = ‖v‖}

def GeodesicExistenceUniqueness : Prop :=
  ∀ (x : M) (v : TangentSpace (model n) x), ∃! γ : ℝ → M,
    CompleteGeodesicWithInitialData x v γ

end

end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
