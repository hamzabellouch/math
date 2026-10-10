import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityMetric
import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityCompleteBound
import OAI.Analysis.KadisonSimilarity.Similarity.PaulsenDischarge
import OAI.Analysis.KadisonSimilarity.Similarity.CompleteNorm

namespace OAI

/-! Paulsen's attained complete bound can be realized by a positive
similarity. Kirchberg takes its self-adjoint logarithm. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem positive_similarity_of_similarity (π : BoundedUnitalHom A H)
    (U : (H →L[ℂ] H)ˣ)
    (hU : ∀ a, (U : H →L[ℂ] H) * π.1 (star a) * (↑U⁻¹ : H →L[ℂ] H) =
      star ((U : H →L[ℂ] H) * π.1 a * (↑U⁻¹ : H →L[ℂ] H))) :
    ∃ S : (H →L[ℂ] H)ˣ, 0 ≤ (S : H →L[ℂ] H) ∧
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ =
        ‖(U : H →L[ℂ] H)‖ * ‖(↑U⁻¹ : H →L[ℂ] H)‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  have hm (a : A) :
      (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) * π.1 (star a) =
        star (π.1 a) * (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) := by
    have h := congrArg (fun X : H →L[ℂ] H =>
      star (U : H →L[ℂ] H) * X * (U : H →L[ℂ] H)) (hU a)
    simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
      Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
      Units.mul_inv_cancel_left, mul_one, one_mul] using h
  obtain ⟨S, hp, hmetric, hn, hi⟩ := exists_positive_sqrt_metric_unit
    (U : H →L[ℂ] H) (↑U⁻¹ : H →L[ℂ] H) U.inv_val U.val_inv
  refine ⟨S, hp, by rw [hn, hi], ?_⟩
  intro a
  have hm' : (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) * π.1 (star a) =
      star (π.1 a) * (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) := by
    rw [hmetric]
    simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using hm a
  have h := congrArg (fun X : H →L[ℂ] H =>
    star (↑S⁻¹ : H →L[ℂ] H) * X * (↑S⁻¹ : H →L[ℂ] H)) hm'
  simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
    Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
    Units.mul_inv_cancel_left, mul_one, one_mul] using h

/-- The positive similarity has condition number exactly the complete norm. -/
theorem exists_positive_similarity_completeNorm (π : BoundedUnitalHom A H)
    (hπ : IsCompletelyBounded π.1) :
    ∃ S : (H →L[ℂ] H)ˣ, 0 ≤ (S : H →L[ℂ] H) ∧
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ = completeNorm π.1 ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  obtain ⟨U, hUnorm, hU⟩ := paulsenSimilarityInput π (completeNorm π.1)
    (completeNorm_nonneg hπ) (completeBound_completeNorm hπ)
  obtain ⟨S, hp, hn, hS⟩ := positive_similarity_of_similarity π U hU
  refine ⟨S, hp, le_antisymm (hn.le.trans hUnorm) ?_, hS⟩
  exact completeNorm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (completeBound_of_similarity π S hS)

end KadisonSimilarity

end

end OAI
