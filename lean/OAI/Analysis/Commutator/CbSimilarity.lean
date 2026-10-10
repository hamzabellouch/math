import Mathlib
import OAI.Analysis.Commutator.CbDilation
import OAI.Analysis.Commutator.FactorGeneratedSpace
import OAI.Analysis.Commutator.FactorMetric
import OAI.Analysis.Commutator.MetricSimilarity

namespace OAI

noncomputable section

noncomputable section

open scoped CStarAlgebra

namespace Kadison.CbFactor

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cbSimilarityPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A

local instance cbSimilarityStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem similarity_of_matrix_bound (π : A →ₐ[ℂ] (H →L[ℂ] H)) {c : ℝ} (hc : 0<c)
    (hπ : HasMatrixBound π.toLinearMap c) :
    ∃ S : (H →L[ℂ] H)ˣ,∀ a : A,
      (S : H →L[ℂ] H)*π (star a)*(↑(S⁻¹) : H →L[ℂ] H)=
        star ((S : H →L[ℂ] H)*π a*(↑(S⁻¹) : H →L[ℂ] H)) := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let := hA
    refine ⟨1,?_⟩
    intro a
    simp [Subsingleton.elim a 0]
  | inr hA =>
    let := hA
    let ρ := representation π.toLinearMap c hc hπ
    let V := leftOperator π.toLinearMap c hc hπ
    let W := rightOperator π.toLinearMap c hc hπ
    have hfactor : ∀ a : A,π a=V.adjoint.comp ((ρ a).comp W) := by
      intro a
      exact factorization π.toLinearMap c hc hπ a
    let L := leftCompression ρ V W
    have hLW : L.comp W=1 := leftCompression_right π ρ V W hfactor
    have hint : ∀ a : A,(π a).comp L=L.comp (ρ a) :=
      leftCompression_intertwines π ρ V W hfactor
    exact similarity_of_metric π (L.comp L.adjoint) (gram_strictlyPositive L W hLW)
      (gram_intertwines π ρ L hint)

end Kadison.CbFactor
end
end

end OAI
