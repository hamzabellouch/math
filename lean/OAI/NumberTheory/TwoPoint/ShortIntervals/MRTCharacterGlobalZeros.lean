import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticLowZeros
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterNonrealZeros

namespace OAI

/-! An all-height effective strip for nonprincipal characters. Its width
retains a polynomial modulus loss; this is not a Vinogradov--Korobov estimate. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

theorem mrt_character_nonprincipal_global_zero_free : ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ t beta : ℝ, 1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ beta →
      DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨cH, hcH, T, hT, hhigh⟩ := mrt_character_nonprincipal_high_zero_free
  obtain ⟨cL, hcL, hlow⟩ := mrt_quadratic_bounded_height_zero_free T
  obtain ⟨cN, hcN, hnonreal⟩ := mrt_character_nonreal_zero_free
  let c := min cH (min cL cN)
  have hc : 0 < c := lt_min hcH (lt_min hcL hcN)
  refine ⟨c, hc, ?_⟩
  intro q _ χ hχ t beta hbeta
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq2 : 1 ≤ (q : ℝ) ^ 2 := by nlinarith
  have hH := mrt_character_height_pos q t
  have hden : mrtCharacterHeight q t ≤ (q : ℝ) ^ 2 * mrtCharacterHeight q t := by
    nlinarith
  by_cases ht : T ≤ |t|
  · apply hhigh q χ hχ t beta ht
    have hd : c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ cH / mrtCharacterHeight q t :=
      (div_le_div_of_nonneg_right (min_le_left cH (min cL cN)) (by positivity)).trans
        (div_le_div_of_nonneg_left hcH.le hH hden)
    linarith
  by_cases hs : χ ^ 2 = 1
  · apply hlow q χ hχ hs t beta (le_of_not_ge ht)
    have hd := div_le_div_of_nonneg_right
      ((min_le_right cH (min cL cN)).trans (min_le_left cL cN))
      (by positivity : 0 ≤ (q : ℝ) ^ 2 * mrtCharacterHeight q t)
    linarith
  · apply hnonreal q χ hs t beta
    have hd : c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ cN / mrtCharacterHeight q t :=
      (div_le_div_of_nonneg_right
        ((min_le_right cH (min cL cN)).trans (min_le_right cL cN))
        (by positivity)).trans (div_le_div_of_nonneg_left hcN.le hH hden)
    linarith

end TwoPointCorrelations

end OAI
