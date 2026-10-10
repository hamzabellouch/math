import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-! # Closed embeddings from compatible global exponential charts

An injective map of finite-dimensional real Lie algebras is closed in linear
coordinates. Compatible global exponential charts transfer that property to
the integrated subgroup map. This supplies the properness required for
fixed-slice packing, without adding a closed-subgroup hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V U N G : Type*}
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [T2Space U]
  [TopologicalSpace N] [TopologicalSpace G]

/-- Global exponential charts turn an injective linear inclusion into a
closed topological embedding. No group-theoretic splitting is required. -/
theorem isClosedEmbedding_of_compatible_charts
    (cN : V ≃ₜ N) (cG : U ≃ₜ G) (j : V →ₗ[ℝ] U)
    (hj : Function.Injective j) (f : N → G)
    (hf : ∀ x, f (cN x) = cG (j x)) : Topology.IsClosedEmbedding f := by
  have he : f = cG ∘ j ∘ cN.symm := by
    funext n
    obtain ⟨x, rfl⟩ := cN.surjective n
    simpa only [Function.comp_apply, cN.symm_apply_apply] using hf x
  rw [he]
  exact cG.isClosedEmbedding.comp
    ((j.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hj)).comp cN.symm.isClosedEmbedding)

/-- The same conclusion with separately named intrinsic exponentials. -/
theorem isClosedEmbedding_of_exponential_compatibility
    (cN : V ≃ₜ N) (cG : U ≃ₜ G) (ExpN : V → N) (ExpG : U → G)
    (hN : ∀ x, cN x = ExpN x) (hG : ∀ x, cG x = ExpG x)
    (j : V →ₗ[ℝ] U) (hj : Function.Injective j) (f : N → G)
    (hf : ∀ x, f (ExpN x) = ExpG (j x)) : Topology.IsClosedEmbedding f := by
  apply isClosedEmbedding_of_compatible_charts cN cG j hj f
  intro x
  rw [hN, hG]
  exact hf x

/-- In particular compact ambient regions have compact sets of subgroup
parameters. This will bound fixed-radius ball multiplicities. -/
theorem isCompact_preimage_of_exponential_compatibility
    (cN : V ≃ₜ N) (cG : U ≃ₜ G) (ExpN : V → N) (ExpG : U → G)
    (hN : ∀ x, cN x = ExpN x) (hG : ∀ x, cG x = ExpG x)
    (j : V →ₗ[ℝ] U) (hj : Function.Injective j) (f : N → G)
    (hf : ∀ x, f (ExpN x) = ExpG (j x))
    {K : Set G} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  (isClosedEmbedding_of_exponential_compatibility cN cG ExpN ExpG hN hG j hj f hf).isProperMap.isCompact_preimage hK

end PolycyclicRecognition

end

end OAI
