import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.FiniteCorners

namespace OAI

section

namespace Pureness
open Filter Topology
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma compress_corner (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) :
    compress h (corner h a) = a := by ext i j; exact corner_apply_cast h a i j

omit [PartialOrder A] [StarOrderedRing A] in
lemma compress_continuous (h : k ≤ l) : Continuous (compress (A := A) h) := by
  change Continuous (fun a : CStarMatrix (Fin l) (Fin l) A =>
    CStarMatrix.ofMatrixL (fun i j =>
      CStarMatrix.ofMatrixL.symm a (Fin.castLE h i) (Fin.castLE h j)))
  exact CStarMatrix.ofMatrixL.continuous.comp (continuous_pi fun row => continuous_pi fun column =>
    (continuous_apply (Fin.castLE h column)).comp
      ((continuous_apply (Fin.castLE h row)).comp CStarMatrix.ofMatrixL.symm.continuous))

omit [PartialOrder A] [StarOrderedRing A] in
lemma compress_mul_corner (h : k ≤ l) (v : CStarMatrix (Fin l) (Fin l) A)
    (a : CStarMatrix (Fin k) (Fin k) A) (i : Fin l) (j : Fin k) :
    (v * corner h a) i (Fin.castLE h j) =
      ∑ t : Fin k, v i (Fin.castLE h t) * a t j := by
  rw [CStarMatrix.mul_apply, sum_corner_support h _ (fun t ht => by
    rw [corner_row_zero h a t _ ht, mul_zero])]
  simp only [corner_apply_cast]

omit [PartialOrder A] [StarOrderedRing A] in
lemma compress_sandwich (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (v : CStarMatrix (Fin l) (Fin l) A) :
    compress h (star v * corner h a * v) = star (compress h v) * a * compress h v := by
  ext i j
  change ((star v * corner h a) * v) (Fin.castLE h i) (Fin.castLE h j) = _
  rw [CStarMatrix.mul_apply, sum_corner_support h _ (fun t ht => by
    have hz : (star v * corner h a) (Fin.castLE h i) t = 0 := by
      simp [CStarMatrix.mul_apply, corner_col_zero h a _ t ht]
    rw [hz, zero_mul])]
  simp_rw [compress_mul_corner]
  simp only [CStarMatrix.star_apply, CStarMatrix.mul_apply, compress]

theorem cuntzSubequiv_corner_iff (h : k ≤ l) (a b : CStarMatrix (Fin k) (Fin k) A) :
    CuntzSubequiv (corner h a) (corner h b) ↔ CuntzSubequiv a b := by
  constructor
  · intro hab
    obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hab
    apply (cuntzSubequiv_iff_sequence _ _).mpr
    refine ⟨fun n => compress h (v n), ?_⟩
    have ht := (compress_continuous h).continuousAt.tendsto.comp hv
    simpa only [Function.comp_def, compress_sandwich, compress_corner] using ht
  · intro hab
    obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hab
    apply (cuntzSubequiv_iff_sequence _ _).mpr
    refine ⟨fun n => corner h (v n), ?_⟩
    have ht := (corner_isometry (A := A) h).continuous.continuousAt.tendsto.comp hv
    change Tendsto (fun n => star (cornerHom h (v n)) * cornerHom h b * cornerHom h (v n))
      atTop (𝓝 (cornerHom h a))
    simpa only [Function.comp_def, map_mul, map_star] using ht

end Pureness
end

end OAI
