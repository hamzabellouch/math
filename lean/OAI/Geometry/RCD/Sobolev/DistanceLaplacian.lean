import OAI.Geometry.RCD.Metric.SquaredDistanceFunctionalBound
import OAI.Geometry.RCD.Metric.BoundedPositiveMeasure
import OAI.Geometry.RCD.Sobolev.DistanceLaplacianInput

namespace OAI

/-! # The local squared-distance input from the RCD condition

The radial first variation gives positivity. A larger-radius cutoff gives
finite mass, and positive extension followed by Riesz--Markov constructs
the defect measure used by the coordinate argument.
-/

open Set Metric MeasureTheory
open scoped NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.localSquaredDistanceInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : LocalSquaredDistanceInput hX := by
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  intro hn κ hκ hK p R hR
  obtain ⟨M, hM, hbound⟩ := hX.squaredDistance_functional_bound hn hκ hK p hR
  let μ := hausdorff n X
  let q := inwardQuadratic μ hX.quadratic p hR.le
  let a := (n : ℝ) + κ * R ^ 2
  let S := compactLipschitzTests (ball p R)
  let F := compactTestEnergy μ hX.quadratic (ball p R) q a
  obtain ⟨σ, hσ, hσrep⟩ := exists_finite_measure_of_positive_bound S F hM hbound
  refine ⟨σ, hσ, hX.inwardSobolev_eikonal hn p hR, ?_⟩
  intro ψ v L hv hs hsupp hrep
  let cv : C_c(X, ℝ) := ⟨⟨v, hv.continuous⟩, hs⟩
  let f : S := ⟨cv.toBoundedContinuousFunction, L, hv, hs, hsupp⟩
  have heq : compactTestSobolev μ hX.quadratic (ball p R) f = ψ := by
    apply Subtype.ext
    apply Lp.ext
    exact (compactTestSobolev_coe μ hX.quadratic (ball p R) f).trans hrep.symm
  have hi := hσrep f hs
  change (∫ x, v x ∂σ) = energyForm μ hX.quadratic q
    (compactTestSobolev μ hX.quadratic (ball p R) f) + a * ∫ x, v x ∂μ at hi
  rw [heq] at hi
  exact hi.symm

end RegularPointCoordinates

end

end OAI
