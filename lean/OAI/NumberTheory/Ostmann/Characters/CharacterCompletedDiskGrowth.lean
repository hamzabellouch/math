import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedRightGrowth
import OAI.NumberTheory.Ostmann.Characters.CharacterRootNumberBound

namespace OAI

/-! # A factorial growth bound for the entire completed L-function -/

namespace Ostmann

open Complex

theorem character_completed_disk_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (N : ℕ) (s : ℂ), ‖s‖ ≤ (N : ℝ) + 1 →
      ‖χ.completed s‖ ≤ 2 * ((N : ℝ) + 2) * ((χ.modulus : ℝ) + 1) *
        (χ.modulus : ℝ) ^ (N + 3) * (C + ((N + 2).factorial : ℝ)) := by
  obtain ⟨C, hC, hright⟩ := character_completed_right_growth
  refine ⟨C, hC, ?_⟩
  intro χ N s hs
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hn : ‖s‖ ≤ ((N + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hh := hright χ (N + 1) s hr hn
    push_cast at hh
    calc
      _ ≤ 2 * ((N : ℝ) + 2) * ((χ.modulus : ℝ) + 1) * (C + ((N + 2).factorial : ℝ)) := by
        simpa only [show N + 1 + 1 = N + 2 by omega,
          show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring] using hh
      _ ≤ _ := by
        have hp : 1 ≤ (χ.modulus : ℝ) ^ (N + 3) := one_le_pow₀ hq
        nlinarith [mul_le_mul_of_nonneg_left hp (by positivity :
          0 ≤ 2 * ((N : ℝ) + 2) * ((χ.modulus : ℝ) + 1) * (C + ((N + 2).factorial : ℝ)))]
  · let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    have hns : ‖1 - s‖ ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
      have hh := norm_sub_le (1 : ℂ) s
      norm_num at hh
      push_cast
      linarith
    have hw := hright χ.inverse (N + 1) (1 - s) (by simp; linarith) hns
    simp only [PrimitiveComplexCharacter.inverse_modulus, Nat.cast_add, Nat.cast_one] at hw
    have hp : ‖(χ.modulus : ℂ) ^ (1 / 2 - s)‖ ≤ (χ.modulus : ℝ) ^ (N + 2) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
      calc
        _ ≤ (χ.modulus : ℝ) ^ ((N + 2 : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hq
          have hh := abs_re_le_norm s
          simp only [sub_re, div_ofNat_re, one_re]
          push_cast
          linarith [(abs_le.mp (hh.trans hs)).1]
        _ = _ := Real.rpow_natCast _ _
    have hf := χ.primitive.completedLFunction_one_sub (1 - s)
    rw [show (1 : ℂ) - (1 - s) = s by ring,
      show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring] at hf
    change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
      DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hf
    rw [hf, norm_mul, norm_mul]
    calc
      _ ≤ (χ.modulus : ℝ) ^ (N + 2) * (χ.modulus : ℝ) *
          (2 * ((N : ℝ) + 1 + 1) * ((χ.modulus : ℝ) + 1) *
            (C + ((N + 1 + 1).factorial : ℝ))) := by
        exact mul_le_mul (mul_le_mul hp χ.rootNumber_norm_le (norm_nonneg _) (by positivity))
          hw (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show N + 1 + 1 = N + 2 by omega,
          show N + 3 = (N + 2) + 1 by omega, pow_succ]
        ring

end Ostmann

end OAI
