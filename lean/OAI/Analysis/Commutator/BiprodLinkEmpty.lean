import Mathlib
import OAI.Analysis.Commutator.BiprodLinkColumn

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G)) (S : Set (Intertwiner N))

lemma compression_empty : compression N S ∅=0 := by
  simp only [compression,finiteProjection,Finset.sum_empty,ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero]

end Kadison.BiprodLinkColumn

end

end
end

end OAI
