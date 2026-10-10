import OAI.Analysis.KadisonSimilarity.Derivation.CyclicColumnTests
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicDecomposition
import OAI.Analysis.KadisonSimilarity.Derivation.DerivationEndgame
import OAI.Analysis.KadisonSimilarity.Similarity.PaulsenDischarge
import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyColumns

namespace OAI

/-! The passage from the uniform commutator bound to similarity through
cyclic summands and their finite-column implementers. -/

noncomputable section
namespace KadisonSimilarity

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Approximate cyclic column factorization for every cyclic representation. -/
structure PublishedDerivationInputs (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : Prop where
  columns : ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)),
    CyclicStarRepresentation σ → CyclicColumnTests σ

/-- The direct regularized-column construction supplies every cyclic case. -/
theorem publishedDerivationInputs : PublishedDerivationInputs.{u,v} A := by
  constructor
  intro K _ _ _ σ hσ
  obtain ⟨Ω, hΩ⟩ := hσ
  exact cyclicColumnTests_of_dense_orbit σ Ω hΩ

variable {H K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Restrict the source of an operator-valued derivation to a closed summand. -/
def derivationColumn (δ : A →L[ℂ] (H →L[ℂ] H)) (U : K →L[ℂ] H) :
    A →L[ℂ] (K →L[ℂ] H) :=
  ((ContinuousLinearMap.compL ℂ K H H).flip U).comp δ

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace K] in
@[simp] theorem derivationColumn_apply
    (δ : A →L[ℂ] (H →L[ℂ] H)) (U : K →L[ℂ] H) (a : A) :
    derivationColumn δ U a = (δ a).comp U := rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The Leibniz identity on a reducing summand follows from its intertwining
inclusion, without requiring the summand to be faithful. -/
theorem derivationColumn_leibniz
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (τ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    (U : K →L[ℂ] H) (hU : ∀ a, (σ a).comp U = U.comp (τ a)) (a b : A) :
    derivationColumn δ U (a * b) =
      (σ a).comp (derivationColumn δ U b) + (derivationColumn δ U a).comp (τ b) := by
  simp only [derivationColumn_apply, hδ, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, hU]

/-- Uniform commutator control, Paulsen similarity and Kaplansky
approximation imply that every bounded derivation is inner. -/
theorem derivation_inner_of_uniformCommutator
    (published : PublishedDerivationInputs.{u,v} A)
    {C : ℝ} (hC : 0 ≤ C) (estimate : UniformCommutatorEstimate.{v} C)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b)) :
    ∃ V : H →L[ℂ] H, ∀ a, δ a = V.comp (σ a) - (σ a).comp V := by
  classical
  let D := cyclicDecompositionData σ.range
  let τ := D.representation σ
  let U (i : D.generators) := (D.summands.inclusion i).toContinuousLinearMap
  let δi (i : D.generators) := derivationColumn δ (U i)
  have hτ (i : D.generators) (a : A) : (σ a).comp (U i) = (U i).comp (τ i a) :=
    D.representation_intertwines σ i a
  have hδi (i : D.generators) (a b : A) :
      δi i (a * b) = (σ a).comp (δi i b) + (δi i a).comp (τ i b) :=
    derivationColumn_leibniz σ (τ i) δ hδ (U i) (hτ i) a b
  have localInner (i : D.generators) : ∃ V : D.Space i →L[ℂ] H,
      (∀ a, δi i a = V.comp (τ i a) - (σ a).comp V) := by
    obtain ⟨V, hV, _⟩ := cyclic_derivation_implementation_of_column_tests
      σ (τ i) (δi i) (hδi i)
      (published.columns (D.Space i) (τ i) (D.representation_cyclic σ i))
      (paulsenSimilarityInput
        (normalizedRectangularRepresentation σ (τ i) (δi i) (hδi i)))
    exact ⟨V, hV⟩
  choose V hV using localInner
  let columns := finiteColumnImplementers_of_summands D.summands σ τ δ V hτ hV
  exact derivation_inner_of_finite_columns σ δ hδ (representationVonNeumannAlgebra σ)
    (mem_representationVonNeumannAlgebra σ) (twoVectorKaplanskyInput σ) columns hC
    (estimate H (representationVonNeumannAlgebra σ))
    (paulsenSimilarityInput (normalizedRectangularRepresentation σ σ δ hδ))

/-- Kirchberg's derivation criterion yields similarity for
every bounded representation of the algebra. -/
theorem algebraSimilarityProperty_of_uniformCommutator
    (published : PublishedDerivationInputs.{u,v} A)
    (kirchberg : KirchbergDerivationCriterion.{u,v} A)
    {C : ℝ} (hC : 0 ≤ C) (estimate : UniformCommutatorEstimate.{v} C) :
    AlgebraSimilarityProperty.{u,v} A := by
  apply kirchberg
  intro K _ _ _ σ hstar _hfaithful δ hδ
  let ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K) := { σ.1 with map_star' := hstar }
  exact derivation_inner_of_uniformCommutator published hC estimate ρ δ hδ

end KadisonSimilarity

end

end OAI
