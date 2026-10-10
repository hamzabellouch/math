import OAI.Analysis.Pureness.Comparison.Comparison
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
namespace CuntzComparison
variable {B : Type*} [NonUnitalCStarAlgebra B]

lemma projection_norm_le_one {p : B} (hp : IsStarProjection p) : ‖p‖ ≤ 1 := by
  have h : ‖p‖ * ‖p‖ = ‖p‖ := by
    rw [← CStarRing.norm_star_mul_self, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  nlinarith [norm_nonneg p]

lemma projection_compression_norm_le {q : B} (hq : IsStarProjection q) (x : B) :
    ‖q * x * q‖ ≤ ‖x‖ := by
  calc
    ‖q * x * q‖ ≤ ‖q * x‖ * ‖q‖ := norm_mul_le _ _
    _ ≤ ‖q * x‖ := mul_le_of_le_one_right (norm_nonneg _) (projection_norm_le_one hq)
    _ ≤ ‖q‖ * ‖x‖ := norm_mul_le _ _
    _ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) (projection_norm_le_one hq)

theorem CuntzSubequiv.exists_corner_witness {a b p q : B}
    (h : CuntzSubequiv a b) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpb : p * b = b) (hbp : b * p = b) (hqa : q * a = a) (haq : a * q = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : B, p * x = x ∧ x * q = x ∧ ‖star x * b * x - a‖ < ε := by
  obtain ⟨X, hX⟩ := cuntzSubequiv_iff_norm.mp h ε hε
  refine ⟨p * X * q, ?_, ?_, ?_⟩
  · simp only [← mul_assoc, hp.isIdempotentElem.eq]
  · simp only [mul_assoc, hq.isIdempotentElem.eq]
  · have heq : star (p * X * q) * b * (p * X * q) - a =
        q * (star X * b * X - a) * q := by
      have hbp' (y : B) : b * (p * y) = b * y := by rw [← mul_assoc, hbp]
      simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        mul_sub, sub_mul]
      simp only [mul_assoc, hpb, hbp', hqa, haq]
    rw [heq]
    exact (projection_compression_norm_le hq _).trans_lt hX
end CuntzComparison

end OAI
