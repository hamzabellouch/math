import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterTrigonometric

namespace OAI

/-! # The 3-4-1 Euler inequality for every complex Dirichlet character -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem complex_character_polynomial_nonneg (v : ℂ) (hv : ‖v‖ ≤ 1) :
    0 ≤ 3 + 4 * v.re + (v * v).re := by
  have hsq := Complex.sq_norm v
  have hn := norm_nonneg v
  simp only [Complex.normSq_apply] at hsq
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (v.re + 1)]

theorem complex_character_trigonometric_term_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I) n).re +
      (LSeries.term (fun n => (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  let u : ℂ := (n : ℂ) ^ (-(t : ℂ) * I)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hv : ‖χ n * u‖ ≤ 1 := by simpa [norm_mul, hu] using χ.norm_le_one n
  have hp := complex_character_polynomial_nonneg (χ n * u) hv
  have hb : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hphase : (n : ℂ) ^ (-((2 * t : ℝ) : ℂ) * I) = u * u := by
    rw [show -((2 * t : ℝ) : ℂ) * I = -(t : ℂ) * I + -(t : ℂ) * I by push_cast; ring]
    exact Complex.cpow_add _ _ (by exact_mod_cast hn)
  have hzero := LSeries_term_vertical (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) n hn σ 0
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one, add_zero] at hzero
  rw [hzero, LSeries_term_vertical _ n hn, LSeries_term_vertical _ n hn, hphase]
  have hsquare : (χ ^ 2) n = χ n * χ n := by simp [pow_two]
  rw [hsquare]
  convert mul_nonneg hb hp using 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem dirichlet_mangoldt_LSeries_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -logDeriv (DirichletCharacter.LFunction χ) s := by
  have he := χ.LSeries_twist_vonMangoldt_eq hs
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs] at he
  exact he.trans (neg_div _ _)

theorem complex_character_trigonometric_sum_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I)).re +
      (LSeries (fun n => (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have h0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have h1 := χ.LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeriesSummable (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((σ : ℂ) + (t : ℂ) * I) at h1
  have h2 := (χ ^ 2).LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ)
  change LSeriesSummable (fun n => (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) at h2
  have hh := tsum_nonneg (L := SummationFilter.unconditional ℕ)
    (complex_character_trigonometric_term_nonneg χ σ t)
  have h0r := (Complex.hasSum_re h0.hasSum).summable
  have h1r := (Complex.hasSum_re h1.hasSum).summable
  have h2r := (Complex.hasSum_re h2.hasSum).summable
  rw [Summable.tsum_add ((h0r.mul_left 3).add (h1r.mul_left 4)) h2r,
    Summable.tsum_add (h0r.mul_left 3) (h1r.mul_left 4), tsum_mul_left, tsum_mul_left,
    ← Complex.re_tsum h0, ← Complex.re_tsum h1, ← Complex.re_tsum h2] at hh
  exact hh

end Ostmann

end OAI
