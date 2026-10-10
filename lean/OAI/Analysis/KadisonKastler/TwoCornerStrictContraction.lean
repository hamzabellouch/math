import OAI.Analysis.KadisonKastler.TomiyamaCornerGeometry
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI

/-! # Strict decrease after removing a bounded-below off-diagonal corner

The spatial innerness argument uses a self-adjoint two-by-two operator
whose off-diagonal corner is bounded below on both summands. Removing
that corner strictly decreases the norm. The estimate is purely a
C-star algebra calculation.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem projection_column_square (p z : A) (hp : IsStarProjection p) :
    star (p * z) * (p * z) + star ((1 - p) * z) * ((1 - p) * z) = star z * z := by
  have hq := hp.one_sub
  calc
    _ = star z * (p * p) * z + star z * ((1 - p) * (1 - p)) * z := by
      simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, mul_assoc]
    _ = star z * p * z + star z * (1 - p) * z := by
      rw [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
    _ = star z * z := by noncomm_ring

theorem norm_projection_diagonal_sq_le (p T : A) (hp : IsStarProjection p)
    (ε : ℝ) (hε : 0 ≤ ε) (hεT : ε ≤ ‖T‖)
    (hcorner : ε ^ 2 • p ≤ star ((1 - p) * (T * p)) * ((1 - p) * (T * p))) :
    ‖p * T * p‖ ^ 2 ≤ ‖T‖ ^ 2 - ε ^ 2 := by
  have hsquare := projection_column_square p (T * p) hp
  have hbound : star (T * p) * (T * p) ≤ ‖T‖ ^ 2 • p := by
    have h := star_left_conjugate_le_conjugate
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq T) p
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, hp.isIdempotentElem.eq] using h
  have ha : star (p * T * p) * (p * T * p) ≤ (‖T‖ ^ 2 - ε ^ 2) • p := by
    have hsum := add_le_add_right hcorner (star (p * (T * p)) * (p * (T * p)))
    rw [hsquare] at hsum
    have h := hsum.trans hbound
    rw [sub_smul]
    exact (le_sub_iff_add_le).mpr (by simpa only [mul_assoc] using h)
  have hc : 0 ≤ ‖T‖ ^ 2 - ε ^ 2 := by nlinarith
  have hp1 : p ≤ (1 : A) := hp.le_one
  have hfinal : star (p * T * p) * (p * T * p) ≤
      algebraMap ℝ A (‖T‖ ^ 2 - ε ^ 2) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact ha.trans (smul_le_smul_of_nonneg_left hp1 hc)
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap _ hc
    (star_mul_self_nonneg _)).mpr hfinal
  simpa only [CStarRing.norm_star_mul_self, pow_two] using hn

theorem norm_two_corner_diagonal_lt (p T : A) (hp : IsStarProjection p)
    (hT : IsSelfAdjoint T) (ε : ℝ) (hε : 0 < ε) (hεT : ε ≤ ‖T‖)
    (hpq : ε ^ 2 • p ≤ star ((1 - p) * (T * p)) * ((1 - p) * (T * p)))
    (hqp : ε ^ 2 • (1 - p) ≤ star (p * (T * (1 - p))) * (p * (T * (1 - p)))) :
    ‖p * T * p + (1 - p) * T * (1 - p)‖ < ‖T‖ := by
  have hpbound := norm_projection_diagonal_sq_le p T hp ε hε.le hεT hpq
  have hqbound := norm_projection_diagonal_sq_le (1 - p) T hp.one_sub ε hε.le hεT
    (by simpa only [sub_sub_cancel] using hqp)
  have hpstrict : ‖p * T * p‖ < ‖T‖ := by
    nlinarith [norm_nonneg (p * T * p)]
  have hqstrict : ‖(1 - p) * T * (1 - p)‖ < ‖T‖ := by
    nlinarith [norm_nonneg ((1 - p) * T * (1 - p))]
  rw [norm_add_eq_max_of_orthogonal_products]
  · exact max_lt hpstrict hqstrict
  · simp only [star_mul, hp.isSelfAdjoint.star_eq, hT.star_eq, mul_assoc,
      ← mul_assoc p (1 - p), hp.mul_one_sub_self, zero_mul, mul_zero]
  · simp only [star_mul, hp.one_sub.isSelfAdjoint.star_eq, hT.star_eq, mul_assoc,
      ← mul_assoc p (1 - p), hp.mul_one_sub_self, zero_mul, mul_zero]

end

end KadisonKastler

end OAI
