import OAI.Analysis.KadisonSimilarity.UnconditionalMain
import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergEndgame

namespace OAI

/-! The universal commutator estimate and finite cyclic reduction imply
similarity for every bounded unital representation. -/

noncomputable section
namespace KadisonSimilarity

universe u v

/-- Theorem `thm:similarity`: every bounded unital complex-algebra
representation of a unital C-star algebra is similar to a star representation. -/
theorem similarityTheorem : SimilarityTheorem.{u,v} := by
  intro A _ H _ _ _ π
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  have : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact similarity_of_uniformCommutator (le_of_lt universalConstant_pos)
    uniformCommutatorEstimate π

/-- The universal estimate implies the derivation criterion for every algebra. -/
theorem kirchbergDerivationCriterion_proved (A : Type u) [CStarAlgebra A] :
    KirchbergDerivationCriterion.{u,v} A := by
  intro _ H _ _ _ π
  exact similarityTheorem A H π

end KadisonSimilarity

end

end OAI
