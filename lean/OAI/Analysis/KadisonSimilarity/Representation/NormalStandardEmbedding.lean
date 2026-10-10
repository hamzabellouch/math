import OAI.Analysis.KadisonSimilarity.Derivation.NormalCyclicGraph

namespace OAI

/-! The standard embedding of a separable concrete finite algebra is
constructed from its faithful normal GNS trace. No vector-realization or
standard-embedding result is an additional hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

local instance normalEmbedding_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

/-- A faithful normal tracial geometry supplies a countable standard embedding. -/
theorem countable_embedding_of_normal_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra) :
    ∃ I : H →ₗᵢ[ℂ] CountableCopies E, ∀ a : M.toStarSubalgebra,
      I.toContinuousLinearMap.comp (a : H →L[ℂ] H) =
        (countableAmplify (G.left a)).comp I.toContinuousLinearMap := by
  let π := M.toStarSubalgebra.subtype
  let D := cyclicDecompositionData π.range
  have hlocal (i : D.generators) : ∃ J : D.Space i →ₗᵢ[ℂ] E, ∀ a,
      J.toContinuousLinearMap.comp (D.representation π i a) =
        (G.left a).comp J.toContinuousLinearMap := by
    apply cyclic_embedding_of_closable_graph G.left (D.representation π i)
      (G.vector 1) (D.generator π i) (D.generator_dense π i)
    exact normal_tracial_cyclic_graph_closable M G τ hτ h1 hf N hN
      (D.representation π i) (D.summands.inclusion i)
      (fun a => (D.representation_intertwines π i a).symm) (D.generator π i)
  choose J hJ using hlocal
  exact countable_embedding_of_cyclic_embeddings π G.left D J hJ

/-- The local Hiai standard-embedding consequence, proved from the
faithful normal trace by spectral truncation and cyclic decomposition. -/
theorem normal_standard_embedding_of_normal_gns
    (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hN : HasNormalGNS τ) :
    HiaiNormalStandardEmbeddingInput τ M.toStarSubalgebra.subtype := by
  exact countable_embedding_of_normal_geometry M (gnsTracialGeometry τ htr)
    τ (fun _ => rfl) h1 (gnsTracialVector_injective τ hf)
    (representationVonNeumannAlgebra τ.gnsStarAlgHom) hN

end KadisonSimilarity

end

end OAI
