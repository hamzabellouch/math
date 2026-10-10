import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaGrowth
import OAI.NumberTheory.Ostmann.Characters.CharacterRootNumberBound

namespace OAI

/-! # Exponential-type growth of the actual character L-function on the left strip -/

namespace Ostmann

open Complex

theorem character_L_left_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖χ.L s‖ ≤ C * (χ.modulus : ℝ) ^ 4 * (2 + |s.im|) * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hG, hGamma, hGammaInv⟩ := characterGamma_growth_bounds
  refine ⟨4 * G ^ 2, by positivity, ?_⟩
  intro χ s hs hs'
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hr : (1 / 2 : ℝ) ≤ (1 - s).re := by simp; linarith
  have hr' : (1 - s).re ≤ (7 / 4 : ℝ) := by simp; linarith
  have hn : ‖1 - s‖ ≤ 2 + |s.im| := by
    calc
      _ ≤ |(1 - s).re| + |(1 - s).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ (1 - s).re)]
        simp only [sub_re, one_re, sub_im, one_im, zero_sub, abs_neg]
        linarith
  have hLi0 := χ.inverse.L_norm_bound_positive (1 - s) (by linarith)
  simp only [PrimitiveComplexCharacter.inverse_modulus] at hLi0
  have hLi : ‖χ.inverse.L (1 - s)‖ ≤ 4 * (χ.modulus : ℝ) * (2 + |s.im|) := by
    apply hLi0.trans
    apply (div_le_iff₀ (by linarith : 0 < (1 - s).re)).mpr
    have hmul : ‖1 - s‖ * ((χ.modulus : ℝ) + 1) ≤
        (2 + |s.im|) * (2 * (χ.modulus : ℝ)) :=
      mul_le_mul hn (by linarith) (by positivity) (by positivity)
    nlinarith [mul_nonneg (by positivity : 0 ≤ (χ.modulus : ℝ) * (2 + |s.im|))
      (sub_nonneg.mpr hr)]
  have hp : ‖(χ.modulus : ℂ) ^ (1 / 2 - s)‖ ≤ (χ.modulus : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    calc
      _ ≤ (χ.modulus : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq (by simp; linarith)
      _ = _ := Real.rpow_two _
  have hGa := hGamma χ.inverse (1 - s) hr hr'
  have hGi := hGammaInv χ s hs hs'
  rw [χ.L_reflection_product s (by linarith)]
  simp only [norm_mul]
  calc
    _ ≤ (χ.modulus : ℝ) ^ 2 * (χ.modulus : ℝ) *
        (4 * (χ.modulus : ℝ) * (2 + |s.im|)) * G * (G * Real.exp (Real.pi * |s.im|)) := by
      gcongr
      exact χ.rootNumber_norm_le
    _ = _ := by ring

end Ostmann

end OAI
