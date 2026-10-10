import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCompletedSquare
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaGrowth

namespace OAI

/-! # A polynomial bound for the entire completed square on the contour strip -/

namespace Ostmann

open Complex

 theorem density_completed_strip_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖χ.completed s‖ ≤ C * ((χ.modulus : ℝ) + 1) ^ 2 * (|s.im| + 2) := by
  obtain ⟨G, hG, hg, _⟩ := characterGamma_growth_bounds
  have hr (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs3 : s.re ≤ 3 / 2) :
      ‖χ.completed s‖ ≤ (2 * G) * ((χ.modulus : ℝ) + 1) * (|s.im| + 2) := by
    have hpos : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ |s.im| + 2 := by
      apply (Complex.norm_le_abs_re_add_abs_im s).trans
      rw [abs_of_pos hpos]
      linarith
    have hl : ‖χ.L s‖ ≤ 2 * ((χ.modulus : ℝ) + 1) * (|s.im| + 2) := by
      apply (χ.L_norm_bound_positive s hpos).trans
      apply (div_le_iff₀ hpos).mpr
      have h := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (χ.modulus : ℝ) + 1)
      have hm := mul_le_mul_of_nonneg_left hs (by positivity :
        0 ≤ 2 * ((χ.modulus : ℝ) + 1) * (|s.im| + 2))
      nlinarith
    rw [χ.completed_eq_L_mul_gamma s hpos, norm_mul]
    exact (mul_le_mul hl (hg χ s hs (by linarith)) (norm_nonneg _) (by positivity)).trans_eq
      (by ring)
  refine ⟨2 * G, by positivity, ?_⟩
  intro χ s hs hs3
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  by_cases hh : 1 / 2 ≤ s.re
  · apply (hr χ s hh hs3).trans
    have hqq : (χ.modulus : ℝ) + 1 ≤ ((χ.modulus : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqq (by positivity)) (by positivity)
  · let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    have hi := hr χ.inverse (1 - s) (by simp; linarith) (by simp; linarith)
    simp only [PrimitiveComplexCharacter.inverse_modulus, sub_im, one_im, zero_sub, abs_neg] at hi
    have hp : ‖(χ.modulus : ℂ) ^ (1 / 2 - s)‖ ≤ χ.modulus := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      apply (Real.rpow_le_rpow_of_exponent_le hq (show (1 / 2 - s).re ≤ 1 by simp; linarith)).trans_eq
      exact Real.rpow_one _
    have hf := χ.primitive.completedLFunction_one_sub (1 - s)
    rw [show (1 : ℂ) - (1 - s) = s by ring,
      show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring] at hf
    change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
      DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hf
    rw [hf, norm_mul, norm_mul, χ.rootNumber_norm_eq_one, mul_one]
    calc
      _ ≤ (χ.modulus : ℝ) * ((2 * G) * ((χ.modulus : ℝ) + 1) * (|s.im| + 2)) :=
        mul_le_mul hp hi (norm_nonneg _) (by positivity)
      _ ≤ _ := by
        have hqq : (χ.modulus : ℝ) * ((χ.modulus : ℝ) + 1) ≤ ((χ.modulus : ℝ) + 1) ^ 2 := by nlinarith
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqq
          (by positivity : 0 ≤ 2 * G)) (by positivity : 0 ≤ |s.im| + 2)
        nlinarith

 theorem density_completed_square_strip_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖densityCompletedSquare χ s‖ ≤ C * ((χ.modulus : ℝ) + 1) ^ 6 * (|s.im| + 2) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_completed_strip_bound
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro χ s hs hs3
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hp : ‖(χ.modulus : ℂ) ^ s‖ ≤ ((χ.modulus : ℝ) + 1) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    calc
      _ ≤ (χ.modulus : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
      _ ≤ _ := by rw [Real.rpow_two]; nlinarith
  rw [densityCompletedSquare, norm_mul, norm_pow]
  apply (mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) (hb χ s hs hs3) 2)
    (by positivity) (by positivity)).trans_eq
  ring

end Ostmann

end OAI
