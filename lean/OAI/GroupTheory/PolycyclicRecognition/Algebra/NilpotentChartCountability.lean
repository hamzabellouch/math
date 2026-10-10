import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel

namespace OAI

/-! # Countability and Haar measure on the chosen nilpotent factors -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLieModel

open Module MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (N : NilpotentLieModel L)

/-- The actual exponential chart transports the countable topology of a
finite-dimensional real vector space to the selected factor. -/
theorem secondCountable_of_chart
    (chart : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₜ N.carrier) :
    SecondCountableTopology N.carrier := by
  let : SecondCountableTopology (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    (finBasis ℝ _).equivFunL.toHomeomorph.secondCountableTopology
  exact chart.symm.isEmbedding.secondCountableTopology

end PolycyclicRecognition.NilpotentLieModel

end

end OAI
