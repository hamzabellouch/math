import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeroSet
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeros

namespace OAI

/-! # Zeros in the enlarged contour disk still lie in the critical strip -/

namespace Ostmann

open Complex Metric

theorem PrimitiveComplexCharacter.L_ne_zero_negative_small (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : -1 < z.re) (hz' : z.re ≤ 0) (hne : z ≠ 0) : χ.L z ≠ 0 := by
  rw [χ.L_eq_completed_mul z hne]
  apply mul_ne_zero (χ.completed_ne_zero_left z hz')
  classical
  unfold PrimitiveComplexCharacter.gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · rw [gammaReal_inverse_factor]
    apply mul_ne_zero hne
    apply mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
    apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re]
    norm_num
    linarith
  · apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

theorem characterContourZeros_critical (χ : PrimitiveComplexCharacter) (t : ℝ)
    (ht : 3 ≤ |t|) (z : ℂ) (hz : z ∈ characterContourZeros χ t) :
    z ∈ complexCharacterZeros χ ∧ |z.im| ≤ |t| + 3 := by
  obtain ⟨hzball, hzero⟩ := (mem_characterContourZeros χ t z).mp hz
  have hn : ‖z - characterZeroCenter t‖ ≤ 21 / 8 := by
    simpa only [mem_closedBall, dist_eq_norm] using hzball
  have hre := (abs_re_le_norm (z - characterZeroCenter t)).trans hn
  have him := (abs_im_le_norm (z - characterZeroCenter t)).trans hn
  simp only [sub_re, sub_im, characterZeroCenter_re, characterZeroCenter_im] at hre him
  have hz0 : z ≠ 0 := by
    intro he
    rw [he] at him
    simp only [zero_im, zero_sub, abs_neg] at him
    linarith
  have hpos : 0 < z.re := by
    by_contra he
    exact χ.L_ne_zero_negative_small z (by linarith [(abs_le.mp hre).1]) (not_lt.mp he) hz0 hzero
  have hlt : z.re < 1 := by
    by_contra he
    exact χ.L_ne_zero_one_le_re z (not_lt.mp he) hzero
  refine ⟨⟨hpos, hlt, hzero⟩, ?_⟩
  calc
    |z.im| = |(z.im - t) + t| := by congr 1; ring
    _ ≤ |z.im - t| + |t| := abs_add_le _ _
    _ ≤ |t| + 3 := by linarith

end Ostmann

end OAI
