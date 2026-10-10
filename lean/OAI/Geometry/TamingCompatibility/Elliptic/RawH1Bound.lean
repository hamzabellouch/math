import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ClosedGraphLift

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart MeasureTheory ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def rawH1 (p : A.centers) (τ : 𝓢(Space,ℝ)) :
    antiEnergy A J α hs ht →L[ℝ] H Space ScalarPair.F 1 :=
  InjectiveLinearLift.continuousLift ((toDistribution Space ScalarPair.F 1).restrictScalars ℝ)
    (toDistribution_injective 1) (rawDistribution A J α hs ht D hD p τ) (fun u => by
      have h := rawDistribution_H1 A J α hs ht D hD p τ u
      have hr : rawDistribution A J α hs ht D hD p τ u ∈
          Set.range (toDistribution Space ScalarPair.F 1) := by
        rw [range_toDistribution]
        exact h
      exact hr)

lemma rawH1_spec (p : A.centers) (τ : 𝓢(Space,ℝ)) (u : antiEnergy A J α hs ht) :
    toDistribution Space ScalarPair.F 1 (rawH1 A J α hs ht D hD p τ u) =
      rawDistribution A J α hs ht D hD p τ u :=
  by
    change ((toDistribution Space ScalarPair.F 1).restrictScalars ℝ)
      (rawH1 A J α hs ht D hD p τ u) = _
    exact InjectiveLinearLift.continuousLift_spec _ _ _ _ _

end TamingCompatibility.GeometricHilbert

end

end OAI
