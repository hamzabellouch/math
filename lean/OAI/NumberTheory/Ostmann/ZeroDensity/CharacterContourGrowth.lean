import OAI.NumberTheory.Ostmann.Characters.CharacterLeftGrowth

namespace OAI

/-! # Actual L-function growth on the fixed strip around the contour -/

namespace Ostmann

open Complex

theorem character_L_contour_strip_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 5 →
      ‖χ.L s‖ ≤ C * (χ.modulus : ℝ) ^ 4 * (6 + |s.im|) * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨A, hA, hleft⟩ := character_L_left_growth
  refine ⟨max A 4, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro χ s hs hs'
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  by_cases hl : s.re ≤ 1 / 2
  · apply (hleft χ s hs hl).trans
    gcongr
    · exact le_max_left _ _
    · norm_num
  · have hpos : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ 5 + |s.im| := by
      apply (Complex.norm_le_abs_re_add_abs_im s).trans
      rw [abs_of_pos hpos]
      linarith
    have hb : ‖χ.L s‖ ≤ 4 * (χ.modulus : ℝ) * (5 + |s.im|) := by
      apply (χ.L_norm_bound_positive s hpos).trans
      apply (div_le_iff₀ hpos).mpr
      have hp : ‖s‖ * ((χ.modulus : ℝ) + 1) ≤ (5 + |s.im|) * (2 * (χ.modulus : ℝ)) :=
        mul_le_mul hn (by linarith) (by positivity) (by positivity)
      nlinarith [mul_nonneg (by positivity : 0 ≤ (χ.modulus : ℝ) * (5 + |s.im|))
        (by linarith : 0 ≤ s.re - 1 / 2)]
    calc
      _ ≤ 4 * (χ.modulus : ℝ) * (5 + |s.im|) := hb
      _ ≤ 4 * (χ.modulus : ℝ) ^ 4 * (6 + |s.im|) := by
        gcongr
        · exact le_self_pow₀ hq (by norm_num)
        · norm_num
      _ ≤ max A 4 * (χ.modulus : ℝ) ^ 4 * (6 + |s.im|) := by
        gcongr
        exact le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
        (Real.one_le_exp (by positivity))

end Ostmann

end OAI
