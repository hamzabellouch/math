import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourGrowth

namespace OAI

/-! # Growth on the fixed disks used for horizontal contour edges -/

namespace Ostmann

open Complex Metric

theorem character_L_contour_disk_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ),
      z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ) →
      ‖χ.L z‖ ≤ C * (χ.modulus : ℝ) ^ 4 * (9 + |t|) *
        Real.exp (Real.pi * (|t| + 3)) := by
  obtain ⟨C, hC, hbound⟩ := character_L_contour_strip_growth
  refine ⟨C, hC, ?_⟩
  intro χ t z hz
  have hn : ‖z - characterZeroCenter t‖ ≤ 11 / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (abs_re_le_norm (z - characterZeroCenter t)).trans hn
  have hi := (abs_im_le_norm (z - characterZeroCenter t)).trans hn
  simp only [sub_re, sub_im, characterZeroCenter] at hr hi
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, mul_zero, add_zero, sub_zero] at hr hi
  norm_num at hr hi
  have hre : -(3 / 4 : ℝ) ≤ z.re ∧ z.re ≤ 5 := by
    have hh := abs_le.mp hr
    constructor <;> linarith
  have him : |z.im| ≤ |t| + 3 := by
    calc
      |z.im| = |(z.im - t) + t| := by congr 1; ring
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 3 := by linarith
  apply (hbound χ z hre.1 hre.2).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him (by positivity))
  · positivity
  · positivity

end Ostmann

end OAI
