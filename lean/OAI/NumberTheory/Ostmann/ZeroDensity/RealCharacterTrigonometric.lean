import OAI.NumberTheory.Ostmann.ZeroDensity.LowHeightZeroBounds

namespace OAI

/-! # The positive trigonometric polynomial for real characters -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem real_character_unit_polynomial (a : ℝ) (ha : |a| ≤ 1) (u : ℂ)
    (hu : ‖u‖ = 1) : 0 ≤ 3 + 4 * a * u.re + (u * u).re := by
  have hsq := Complex.sq_norm u
  rw [hu] at hsq
  simp only [one_pow, Complex.normSq_apply] at hsq
  rw [Complex.mul_re]
  rcases le_total 0 u.re with hr | hr
  · have hm := mul_nonneg (show 0 ≤ a + 1 by linarith [(abs_le.mp ha).1]) hr
    nlinarith [sq_nonneg (u.re - 1)]
  · have hm := mul_nonneg (show 0 ≤ 1 - a by linarith [(abs_le.mp ha).2]) (neg_nonneg.mpr hr)
    nlinarith [sq_nonneg (u.re + 1)]

theorem LSeries_term_vertical (c : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) (σ t : ℝ) :
    LSeries.term c ((σ : ℂ) + (t : ℂ) * I) n =
      c n * ((n : ℝ) ^ (-σ) : ℝ) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  rw [show -((σ : ℂ) + (t : ℂ) * I) = (-(σ : ℝ) : ℂ) + (-(t : ℂ) * I) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hn)]
  have hr : (n : ℂ) ^ (-(σ : ℂ)) = ((n : ℝ) ^ (-σ) : ℝ) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
  rw [hr]
  ring

theorem real_character_trigonometric_term_nonneg (χ : PrimitiveRealCharacter) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I) n).re +
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  let u : ℂ := (n : ℂ) ^ (-(t : ℂ) * I)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have ha : |χ.character n| ≤ 1 := by simpa [Real.norm_eq_abs] using χ.character.norm_le_one n
  have hp := real_character_unit_polynomial (χ.character n) ha u hu
  have hb : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hphase : (n : ℂ) ^ (-((2 * t : ℝ) : ℂ) * I) = u * u := by
    rw [show -((2 * t : ℝ) : ℂ) * I = -(t : ℂ) * I + -(t : ℂ) * I by push_cast; ring]
    exact Complex.cpow_add _ _ (by exact_mod_cast hn)
  have hzero := LSeries_term_vertical (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) n hn σ 0
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one, add_zero] at hzero
  rw [hzero, LSeries_term_vertical _ n hn, LSeries_term_vertical _ n hn, hphase]
  simp only [PrimitiveRealCharacter.complexCharacter, MulChar.ringHomComp_apply,
    Complex.ofRealHom_eq_coe, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, sub_zero, add_zero]
  change 0 ≤ 3 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) +
    4 * (χ.character n * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * u.re) +
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * (u * u).re
  convert mul_nonneg hb hp using 1
  ring

/-- The Euler series inherits positivity term by term; no prime distribution
input or zero-free assumption is used. -/
theorem real_character_trigonometric_sum_nonneg (χ : PrimitiveRealCharacter)
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I)).re +
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have h0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have h1 := χ.complexCharacter.LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeriesSummable (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((σ : ℂ) + (t : ℂ) * I) at h1
  have h2 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ)
  have hh := tsum_nonneg (L := SummationFilter.unconditional ℕ)
    (real_character_trigonometric_term_nonneg χ σ t)
  have h0r := (Complex.hasSum_re h0.hasSum).summable
  have h1r := (Complex.hasSum_re h1.hasSum).summable
  have h2r := (Complex.hasSum_re h2.hasSum).summable
  rw [Summable.tsum_add ((h0r.mul_left 3).add (h1r.mul_left 4)) h2r,
    Summable.tsum_add (h0r.mul_left 3) (h1r.mul_left 4), tsum_mul_left, tsum_mul_left,
    ← Complex.re_tsum h0, ← Complex.re_tsum h1, ← Complex.re_tsum h2] at hh
  exact hh

end Ostmann

end OAI
