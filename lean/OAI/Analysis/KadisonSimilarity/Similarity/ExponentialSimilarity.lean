import OAI.Analysis.KadisonSimilarity.Similarity.PositiveSimilarity
import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergExponentialNorm

namespace OAI

/-! The optimal positive similarity, written in the exponential form used
in Kirchberg, J. Operator Theory 36 (1996), Proposition 1. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace
open scoped CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance exponentialSimilarityRatAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _

theorem exists_exponential_similarity (π : BoundedUnitalHom A H)
    (hπ : IsCompletelyBounded π.1) :
    ∃ (t : H →L[ℂ] H) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)), IsSelfAdjoint t ∧
      (∀ a, π.1 a = exp (-t) * σ a * exp t) ∧
      ‖exp (-t)‖ * ‖exp t‖ = completeNorm π.1 := by
  obtain ⟨S, hp, hn, hS⟩ := exists_positive_similarity_completeNorm π hπ
  let t := CFC.log (S : H →L[ℂ] H)
  have ht : IsSelfAdjoint t := IsSelfAdjoint.log
  have he : exp t = (S : H →L[ℂ] H) := CFC.exp_log _ (S.isUnit.isStrictlyPositive hp)
  have hi : exp (-t) = (↑S⁻¹ : H →L[ℂ] H) := by
    have h : exp (-t) * (S : H →L[ℂ] H) = 1 := by
      rw [← he, ← exp_add_of_commute (Commute.refl t).neg_left,
        neg_add_cancel, NormedSpace.exp_zero]
    have h' := congrArg (fun X : H →L[ℂ] H => X * (↑S⁻¹ : H →L[ℂ] H)) h
    simpa only [mul_assoc, Units.mul_inv, mul_one, one_mul] using h'
  refine ⟨t, similarityStarRepresentation π S hS, ht, ?_, ?_⟩
  · intro a
    simp only [he, hi, similarityStarRepresentation, similarityRepresentation,
      StarAlgHom.coe_mk, mul_assoc, Units.inv_mul_cancel_left,
      Units.inv_mul, mul_one]
  · rw [he, hi, mul_comm]
    exact hn

end KadisonSimilarity

end

end OAI
