import OAI.Analysis.KadisonSimilarity.Representation.CentralDecomposition
import OAI.Analysis.KadisonSimilarity.Representation.NonseparableReduction
import OAI.Analysis.KadisonSimilarity.Derivation.FinalDerivations
import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityUniverseTransfer
import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import OAI.Analysis.KadisonSimilarity.Similarity.ArvesonDischarge

namespace OAI

/-! Uniform commutator estimates, hyperreflexivity, and similarity
from central factor models and derivation implementation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A central direct-integral model with separable Hilbert fibers and the
finite or properly infinite factor structure. -/
structure PublishedSeparableModel (P : VonNeumannAlgebra H) where
  Ω : Type u
  [measurable : MeasurableSpace Ω]
  measure : Measure Ω
  K : Ω → Type u
  [normed : ∀ a, NormedAddCommGroup (K a)]
  [inner : ∀ a, InnerProductSpace ℂ (K a)]
  [complete : ∀ a, CompleteSpace (K a)]
  /-- The standard direct-integral decomposition of a separable space has
  separable Hilbert fibers (Blackadar, III.1.6.1–4). -/
  [separableFiber : ∀ a, TopologicalSpace.SeparableSpace (K a)]
  decomposition : CentralDecompositionData measure K P
  cases : ∀ᵐ a ∂measure, PublishedFactorCasesInput (decomposition.algebra a)

attribute [instance] PublishedSeparableModel.measurable PublishedSeparableModel.normed
  PublishedSeparableModel.inner PublishedSeparableModel.complete
  PublishedSeparableModel.separableFiber

/-- Existence of central factor models for separable represented algebras. -/
structure PublishedUniformInputs : Prop where
  separable : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K] (P : VonNeumannAlgebra K),
    Nonempty (PublishedSeparableModel P)

/-- The universal matrix estimate with the manuscript's fixed constant. -/
theorem uniformCommutatorEstimate_of_published (inputs : PublishedUniformInputs.{u}) :
    UniformCommutatorEstimate.{u} universalConstant := by
  apply uniformCommutatorEstimate_of_separable (le_of_lt universalConstant_pos) _ (by
    intro K _ _ _ _ A _ _ _ σ
    exact twoVectorKaplanskyInput σ)
  intro K _ _ _ _ P
  obtain ⟨D⟩ := inputs.separable K P
  exact commutatorEstimate_of_centralDecomposition D.decomposition
    (spectralStepApproximation (vonNeumannCenter P)) D.cases
    (Filter.Eventually.of_forall fun _ => dicksonTwoBound_proved)

/-- Theorem `thm:universal`, conditional only on the named published inputs. -/
theorem universalCommutatorTheorem_of_published (inputs : PublishedUniformInputs.{u}) :
    UniversalCommutatorTheorem.{u} :=
  ⟨universalConstant, le_of_lt universalConstant_pos,
    uniformCommutatorEstimate_of_published inputs⟩

/-- Theorem `thm:similarity`, using Kirchberg's criterion after the proved
bounded-derivation implementation. The canonical spectral order introduces
no restriction on the C-star algebra. -/
theorem similarityTheorem_sameUniverse_of_published (inputs : PublishedUniformInputs.{u})
    (kirchberg : ∀ (A : Type u) [CStarAlgebra A], KirchbergDerivationCriterion.{u,u} A) :
    SimilarityTheorem.{u,u} := by
  intro A _ K _ _ _ π
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  have : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact algebraSimilarityProperty_of_uniformCommutator publishedDerivationInputs (kirchberg A)
    (le_of_lt universalConstant_pos) (uniformCommutatorEstimate_of_published inputs) K π

/-- The full similarity statement, with unrelated source and Hilbert-space
universes. The published faithful-representation criterion is used only in
one common universe containing both; the actual implementing operator is
then transported back. -/
theorem similarityTheorem_of_published
    (inputs : PublishedUniformInputs.{max u v})
    (kirchberg : ∀ (A : Type (max u v)) [CStarAlgebra A],
      KirchbergDerivationCriterion.{max u v, max u v} A) :
    SimilarityTheorem.{u,v} :=
  SimilarityUniverseTransfer.similarityTheorem_of_commonUniverse
    (similarityTheorem_sameUniverse_of_published inputs kirchberg)

/-- Corollary `cor:hyperreflexivity`, with the same universal constant and
the commutant-distance formula now proved. -/
theorem universalHyperreflexivity_of_published (inputs : PublishedUniformInputs.{u}) :
    UniversalHyperreflexivity.{u} universalConstant := by
  intro K _ _ _ M T
  exact hyperreflexivity_of_spectralSteps_and_arveson M (spectralStepApproximation M.commutant) T
    (le_of_lt universalConstant_pos) (arvesonDistanceFormula M T)
    (uniformCommutatorEstimate_of_published inputs K M.commutant)

end KadisonSimilarity

end

end OAI
