import OAI.Analysis.KadisonKastler.ScalarBoundaryMean

namespace OAI

/-! # The published scalar boundary input

Bader--Furman, *Boundaries, rigidity of representations, and Lyapunov
exponents*, Proceedings ICM 2014, III, 71--96: Definition 2.3 (p. 73),
Remarks 2.4(1),(4) (pp. 73--74), and Theorem 2.7 (p. 75).
Adams--Elliott--Giordano, *Amenable Actions of Groups*, Transactions AMS
344 (1994), 803--822, Theorem 3.4 (pp. 810--811), supplies the scalar
conditional expectations for both amenable actions.

The means below act on actual scalar L-infinity classes. No operator
correction or algebra isomorphism is part of this input.
-/

namespace KadisonKastler

open MeasureTheory

universe u

/-- The application-specific existence statement for a countable group:
a probability boundary with scalar means for the original and separate
product actions, and unitary double ergodicity for the diagonal action. -/
def PublishedBoundary : Prop :=
  ∀ (G : Type u) [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G],
    ∃ (D : Type u) (_ : MeasurableSpace D) (μ : Measure D)
      (_ : IsProbabilityMeasure μ) (α : NonsingularAction G D μ),
      Nonempty (ScalarBoundaryMean α) ∧
      Nonempty (ScalarBoundaryMean α.prod) ∧
      UnitaryDoubleErgodic.{u, u, u} α

end KadisonKastler

end OAI
