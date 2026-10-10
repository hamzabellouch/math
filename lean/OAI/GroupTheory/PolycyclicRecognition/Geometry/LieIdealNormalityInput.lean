import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationInput
import Mathlib.Algebra.Lie.Ideal

namespace OAI

/-! # The published ideal-to-normal-subgroup implication

J. M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218,
Springer (2013), Theorem 20.28, pp.535–536 (Ideals and Normal Subgroups).
https://doi.org/10.1007/978-1-4419-9982-5

Only the forward implication, for an embedded connected nilpotent subgroup,
is retained. The actual differential is required to identify its Lie algebra
with the given ideal. No ambient factorization or height assertion is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- Exact connected embedded nilpotent specialization of Lee's ideal
criterion. All Lie algebras here are the actual tangent Lie algebras. -/
def NilpotentIdealNormalityInput : Prop :=
  PreconnectedSpace N → PreconnectedSpace G →
  LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N) →
    ∀ (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G))
      (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G)
      (ι : N →* G),
      Function.Injective j → Topology.IsClosedEmbedding ι →
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι →
      (∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x) →
      Set.range j = (I : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) → ι.range.Normal

end PolycyclicRecognition

end

end OAI
