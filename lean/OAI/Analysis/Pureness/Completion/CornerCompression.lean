import OAI.Analysis.Pureness.Divisibility.CornerComparison
import OAI.Analysis.Pureness.Divisibility.CornerRanks

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A]
variable {k l : ℕ}

noncomputable def cornerProjection (_h : k ≤ l) : CStarMatrix (Fin l) (Fin l) A :=
  diagonalMatrixHom fun i => if i.val < k then 1 else 0

lemma cornerProjection_eq (h : k ≤ l) :
    cornerProjection (A := A) h = corner h (1 : CStarMatrix (Fin k) (Fin k) A) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k <;> simp [cornerProjection, diagonalMatrixHom_apply, corner, hi]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [cornerProjection, diagonalMatrixHom_apply, corner,
      hij, Fin.ext_iff, hv]

lemma cornerProjection_star (h : k ≤ l) : star (cornerProjection (A := A) h) = cornerProjection h := by
  rw [cornerProjection_eq]
  change star (cornerHom h 1) = cornerHom h 1
  rw [← map_star, star_one]

lemma cornerProjection_norm_le [PartialOrder A] [StarOrderedRing A] (h : k ≤ l) :
    ‖cornerProjection (A := A) h‖ ≤ 1 := by
  rw [cornerProjection_eq, corner_norm]
  cases subsingleton_or_nontrivial (CStarMatrix (Fin k) (Fin k) A)
  · rw [Subsingleton.elim (1 : CStarMatrix (Fin k) (Fin k) A) 0, norm_zero]; exact zero_le_one
  · exact le_of_eq (norm_one)

lemma cornerProjection_mul (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) (i j : Fin l) :
    (cornerProjection (A := A) h * a) i j = if i.val < k then a i j else 0 := by
  simp [CStarMatrix.mul_apply, cornerProjection, diagonalMatrixHom_apply, ite_mul]

lemma mul_cornerProjection (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) (i j : Fin l) :
    (a * cornerProjection (A := A) h) i j = if j.val < k then a i j else 0 := by
  simp [CStarMatrix.mul_apply, cornerProjection, diagonalMatrixHom_apply, mul_ite]

lemma corner_compress (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) :
    corner h (compress h a) = cornerProjection h * a * cornerProjection h := by
  ext i j
  rw [mul_cornerProjection, cornerProjection_mul]
  by_cases hi : i.val < k <;> by_cases hj : j.val < k <;>
    simp [corner, compress, hi, hj]

variable [PartialOrder A] [StarOrderedRing A]

theorem compress_norm_le (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) :
    ‖compress h a‖ ≤ ‖a‖ := by
  rw [← corner_norm h, corner_compress]
  calc
    _ ≤ ‖cornerProjection (A := A) h‖ * ‖a‖ * ‖cornerProjection (A := A) h‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (cornerProjection_norm_le h) (norm_nonneg _))
      (cornerProjection_norm_le h) (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

theorem corner_compress_cuntz (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) :
    CuntzSubequiv (corner h (compress h a)) a := by
  rw [corner_compress]
  simpa only [cornerProjection_star] using cuntzSubequiv_conjugate a (cornerProjection (A := A) h)
end CuntzPureness

end OAI
