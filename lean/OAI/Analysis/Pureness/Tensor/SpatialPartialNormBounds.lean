import OAI.Analysis.Pureness.Tensor.SpatialPartialTranslations
import OAI.Analysis.Pureness.Operators.AbstractPartialNormBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped CStarAlgebra
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))
attribute [local instance] spatialPartialOperatorOrder spatialPartialOperatorStarOrdered

lemma single_square_norm_le_row {n : ℕ} (a : Fin n → A) (i : Fin n) :
    ‖star (a i) * a i‖ ≤ ‖∑ j, a j * star (a j)‖ := by
  have hi : a i * star (a i) ≤ ∑ j, a j * star (a j) :=
    Finset.single_le_sum (fun j _ => mul_star_self_nonneg (a j)) (Finset.mem_univ i)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hi (mul_star_self_nonneg (a i))
  simpa only [CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self] using hn

theorem spatialFreePartial_norm_bounds {n : ℕ} (a : Fin n → A)
    (ha : (∑ i, star (a i) * a i) = 1)
    (hr : ‖∑ i, a i * star (a i)‖ ≤ 1 / 16) :
    ‖star (spatialFreeCreationSum α a) * spatialFreeCreationSum α a - 1‖ ≤ 1 / 16 ∧
      ‖spatialFreeCreationSum α a‖ ≤ 1 ∧ ‖spatialFreeCancellationSum α a‖ ≤ 1 / 4 := by
  apply abstractPartialNormBounds
    (spatialFreeCreationSum α a) (spatialFreeCancellationSum α a)
    (spatialLetterSum α false (fun i => star (a i) * a i))
    (spatialLetterSum α true (fun i => a i * star (a i)))
    (spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α (∑ i, a i * star (a i)))
  · exact spatialLetterSum_nonneg α false _ (fun i => star_mul_self_nonneg (a i))
  · exact spatialLetterSum_nonneg α true _ (fun i => mul_star_self_nonneg (a i))
  · exact spatialLetterSum_norm_le α false _ _ (by norm_num)
      (fun i => star_mul_self_nonneg (a i)) (fun i => (single_square_norm_le_row a i).trans hr)
  · exact (spatialPartialLeft_norm_le α _).trans hr
  · rw [spatialFreeCreationSum_square, ha, map_one]
  · exact spatialFreeCancellationSum_square α a
end CuntzPureness

end

end OAI
