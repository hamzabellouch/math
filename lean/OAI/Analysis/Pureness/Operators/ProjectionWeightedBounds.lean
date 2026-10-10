import OAI.Analysis.Pureness.Operators.OrthogonalOperatorSums
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
noncomputable section
namespace CuntzPureness
variable {B ι : Type*} [CStarAlgebra B] [Fintype ι]

theorem orthogonal_projection_sum (p : ι → B) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0) : IsStarProjection (∑ i, p i) := by
  have hs : star (∑ i, p i) = ∑ i, p i := by
    simp only [star_sum, fun i => (hp i).isSelfAdjoint.star_eq]
  have hm := star_sum_mul_sum_of_orthogonal p (fun i j hij => by
    rw [(hp i).isSelfAdjoint.star_eq]; exact ho i j hij)
  rw [hs] at hm
  simp only [fun i => (hp i).isSelfAdjoint.star_eq, fun i => (hp i).isIdempotentElem.eq] at hm
  exact ⟨hm, hs⟩

variable [PartialOrder B] [StarOrderedRing B]

theorem orthogonal_projection_sum_le_one (p : ι → B) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0) : (∑ i, p i) ≤ 1 :=
  sub_nonneg.mp (orthogonal_projection_sum p hp ho).one_sub.nonneg

theorem orthogonal_positive_compressions_le (p x : ι → B) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ i, IsStarProjection (p i)) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ C) :
    (∑ i, p i * x i * p i) ≤ C • (1 : B) := by
  calc
    _ ≤ ∑ i, C • p i := by
      apply Finset.sum_le_sum
      intro i _
      have hi := CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := p i) (b := x i) (hx i).isSelfAdjoint
      rw [(hp i).isSelfAdjoint.star_eq, (hp i).isIdempotentElem.eq] at hi
      exact hi.trans (smul_le_smul_of_nonneg_right (hxn i) (hp i).nonneg)
    _ ≤ C • (1 : B) := by
      rw [← Finset.smul_sum]
      exact smul_le_smul_of_nonneg_left (orthogonal_projection_sum_le_one p hp ho) hC

theorem norm_orthogonal_positive_compressions_le (p x : ι → B) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ i, IsStarProjection (p i)) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ C) :
    ‖∑ i, p i * x i * p i‖ ≤ C := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hC ?_).mpr
  · simpa only [Algebra.algebraMap_eq_smul_one] using
      orthogonal_positive_compressions_le p x C hC hp ho hx hxn
  · apply Finset.sum_nonneg
    intro i _
    simpa only [(hp i).isSelfAdjoint.star_eq] using star_left_conjugate_nonneg (hx i) (p i)
end CuntzPureness

end

end OAI
