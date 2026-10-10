import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialEmbedding
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Lie.Nilpotent

namespace OAI

/-! # Published integration input for nilpotent subalgebras

J. M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218,
Springer (2013), Theorem 20.19 (p.530) and Proposition 20.8(g) (p.520).
https://doi.org/10.1007/978-1-4419-9982-5
Theorem 20.19 integrates a Lie algebra homomorphism from a simply connected
Lie group; Proposition 20.8(g) supplies exponential compatibility. We retain
only nilpotent source groups, the smooth homomorphism, its prescribed
differential and its action on the intrinsic exponential. Closedness is proved separately from the
already available global charts, rather than added to the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- Nilpotent-domain specialization of Lie's integration theorem and
naturality of the exponential. -/
def NilpotentLieIntegrationInput : Prop :=
  SimplyConnectedSpace N → LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N) →
    ∀ (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
      (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G),
      IsGroupExponential ExpN → IsGroupExponential ExpG →
      ∃ ι : N →* G, ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
        (∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x) ∧
        ∀ x, ι (ExpN x) = ExpG (j x)

/-- Integration plus the two global charts yields a closed subgroup map
whose range is exactly the exponential image of the Lie-algebra range. -/
theorem exists_closed_integration
    [SimplyConnectedSpace N]
    (integrate : NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G))
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N))
    (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (hj : Function.Injective j)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
    (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)
    (hExpN : IsGroupExponential ExpN) (hExpG : IsGroupExponential ExpG)
    (cN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hcN : ∀ x, cN x = ExpN x)
    (cG : GroupLieAlgebra (𝓘(ℝ, EG)) G ≃ₜ G) (hcG : ∀ x, cG x = ExpG x) :
    ∃ ι : N →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
      (∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x) ∧
      (∀ x, ι (ExpN x) = ExpG (j x)) ∧ Set.range ι = ExpG '' Set.range j := by
  obtain ⟨ι, hsmooth, hderiv, hι⟩ := integrate inferInstance hnil j ExpN ExpG hExpN hExpG
  refine ⟨ι, isClosedEmbedding_of_exponential_compatibility cN cG ExpN ExpG hcN hcG
    j.toLinearMap hj ι hι, hsmooth, hderiv, hι, ?_⟩
  ext g
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨x, hx⟩ := cN.surjective n
    rw [hcN] at hx
    exact ⟨j x, ⟨x, rfl⟩, (hι x).symm.trans (congrArg ι hx)⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨ExpN x, hι x⟩

end PolycyclicRecognition

end

end OAI
