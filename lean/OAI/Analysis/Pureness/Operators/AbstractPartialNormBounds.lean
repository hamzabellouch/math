import OAI.Analysis.Pureness.Operators.ProjectionWeightedBounds
import Mathlib.Tactic.Linarith

namespace OAI
noncomputable section
namespace CuntzPureness
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma abstractPartialNormBounds (v w D E R : B) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hDn : ‖D‖ ≤ 1 / 16) (hRn : ‖R‖ ≤ 1 / 16)
    (hv : star v * v = 1 - D) (hw : w * star w = R - E) :
    ‖star v * v - 1‖ ≤ 1 / 16 ∧ ‖v‖ ≤ 1 ∧ ‖w‖ ≤ 1 / 4 := by
  have hnear : ‖star v * v - 1‖ ≤ 1 / 16 := by
    have he : 1 - D - 1 = -D := by abel
    rwa [hv, he, norm_neg]
  have hvn : ‖v‖ ≤ 1 := by
    have hle : star v * v ≤ 1 := by rw [hv]; exact sub_le_self _ hD
    have hh := (CStarAlgebra.norm_le_one_iff_of_nonneg (star v * v)
      (star_mul_self_nonneg v)).mpr hle
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg v]
  have hwn : ‖w‖ ≤ 1 / 4 := by
    have hle : w * star w ≤ R := by rw [hw]; exact sub_le_self _ hE
    have hh := (CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (mul_star_self_nonneg w)).trans hRn
    rw [CStarRing.norm_self_mul_star] at hh
    nlinarith [norm_nonneg w]
  exact ⟨hnear, hvn, hwn⟩
end CuntzPureness

end

end OAI
