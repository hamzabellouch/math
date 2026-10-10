import Mathlib
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicColumns

variable {A ι H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : DecidableEq ι := Classical.decEq ι

lemma diagonal_commutes_matrixRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (X : CStarMatrix ι ι A)
    (hT : ∀ i j,T*σ (X i j)=σ (X i j)*T) :
    OperatorAmplification.diagonal (H:=H) ι T*matrixRepresentation σ X=
      matrixRepresentation σ X*OperatorAmplification.diagonal (H:=H) ι T := by
  ext v i
  simp only [mul_apply_eq_comp,OperatorAmplification.diagonal_apply,matrixRepresentation,
    StarAlgHom.coe_mk,matrixAction_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun R : H →L[ℂ] H => R (v j)) (hT i j)

end Kadison.CyclicColumns

end

end
end

end OAI
