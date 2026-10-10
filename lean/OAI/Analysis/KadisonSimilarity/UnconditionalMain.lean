import OAI.Analysis.KadisonSimilarity.Representation.SeparableModelConstruction

namespace OAI

/-! Uniform matrix commutator estimates and universal hyperreflexivity,
with the numerical constant obtained from the factor estimates and central decomposition. -/

noncomputable section
namespace KadisonSimilarity

universe u v

/-- The manuscript's uniform matrix commutator estimate, with no remaining
published structural hypotheses. -/
theorem uniformCommutatorEstimate : UniformCommutatorEstimate.{u} universalConstant :=
  uniformCommutatorEstimate_of_published publishedUniformInputs

/-- Theorem `thm:universal` of the manuscript. -/
theorem universalCommutatorTheorem : UniversalCommutatorTheorem.{u} :=
  universalCommutatorTheorem_of_published publishedUniformInputs

/-- Corollary `cor:hyperreflexivity` of the manuscript. -/
theorem universalHyperreflexivity : UniversalHyperreflexivity.{u} universalConstant :=
  universalHyperreflexivity_of_published publishedUniformInputs

/-- Kirchberg's derivation criterion and the universal commutator estimate
imply similarity, with independent source and Hilbert universes. -/
theorem similarityTheorem_of_kirchberg
    (kirchberg : ∀ (A : Type (max u v)) [CStarAlgebra A],
      KirchbergDerivationCriterion.{max u v, max u v} A) : SimilarityTheorem.{u,v} :=
  similarityTheorem_of_published publishedUniformInputs kirchberg

end KadisonSimilarity

end

end OAI
