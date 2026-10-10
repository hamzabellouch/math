import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterTrigonometric
import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterLifts

namespace OAI

/-! # The positive Euler combination for two real characters -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem self_inverse_character_im_zero {N : ℕ} [NeZero N]
    (a : DirichletCharacter ℂ N) (ha : a⁻¹ = a) (n : ℕ) : (a n).im = 0 := by
  have hh : star a = a := (MulChar.star_eq_inv a).trans ha
  have hv := congrArg (fun χ : DirichletCharacter ℂ N => (χ n).im) hh
  simp at hv
  linarith

theorem real_character_pair_term_nonneg {N : ℕ} (a b : DirichletCharacter ℂ N)
    (ha : ∀ n : ℕ, (a n).im = 0) (hb : ∀ n : ℕ, (b n).im = 0) (σ : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term (fun n => a n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term (fun n => b n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term (fun n => (a * b) n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  have h1 : 0 ≤ 1 + (a n).re := by linarith [(Complex.abs_re_le_norm (a n)).trans (a.norm_le_one n), neg_abs_le (a n).re]
  have h2 : 0 ≤ 1 + (b n).re := by linarith [(Complex.abs_re_le_norm (b n)).trans (b.norm_le_one n), neg_abs_le (b n).re]
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have he (f : ℕ → ℂ) : LSeries.term f (σ : ℂ) n = f n * ((n : ℝ) ^ (-σ) : ℝ) := by
    simpa using LSeries_term_vertical f n hn σ 0
  rw [he, he, he, he]
  simp only [MulChar.mul_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, ha, hb, mul_zero, zero_mul, sub_zero, add_zero]
  convert mul_nonneg hw (mul_nonneg h1 h2) using 1
  ring

theorem real_character_pair_sum_nonneg {N : ℕ} (a b : DirichletCharacter ℂ N)
    (ha : ∀ n : ℕ, (a n).im = 0) (hb : ∀ n : ℕ, (b n).im = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      (LSeries (fun n => a n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      (LSeries (fun n => b n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      (LSeries (fun n => (a * b) n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re := by
  have h0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have h1 := a.LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) hσ
  have h2 := b.LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) hσ
  have h3 := (a * b).LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) hσ
  change LSeriesSummable (fun n => a n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) at h1
  change LSeriesSummable (fun n => b n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) at h2
  change LSeriesSummable (fun n => (a * b) n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) at h3
  have hh := tsum_nonneg (L := SummationFilter.unconditional ℕ) (real_character_pair_term_nonneg a b ha hb σ)
  have h0r := (Complex.hasSum_re h0.hasSum).summable
  have h1r := (Complex.hasSum_re h1.hasSum).summable
  have h2r := (Complex.hasSum_re h2.hasSum).summable
  have h3r := (Complex.hasSum_re h3.hasSum).summable
  rw [Summable.tsum_add ((h0r.add h1r).add h2r) h3r,
    Summable.tsum_add (h0r.add h1r) h2r, Summable.tsum_add h0r h1r,
    ← Complex.re_tsum h0, ← Complex.re_tsum h1, ← Complex.re_tsum h2,
    ← Complex.re_tsum h3] at hh
  exact hh

theorem real_character_pair_logDeriv_le {N : ℕ} [NeZero N] (a b : DirichletCharacter ℂ N)
    (ha : a⁻¹ = a) (hb : b⁻¹ = b) (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv (DirichletCharacter.LFunction a) (σ : ℂ)).re +
      (logDeriv (DirichletCharacter.LFunction b) (σ : ℂ)).re ≤
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re -
          (logDeriv (DirichletCharacter.LFunction (a * b)) (σ : ℂ)).re := by
  have hh := real_character_pair_sum_nonneg a b (self_inverse_character_im_zero a ha)
    (self_inverse_character_im_zero b hb) σ hσ
  rw [dirichlet_mangoldt_LSeries_eq a _ hσ, dirichlet_mangoldt_LSeries_eq b _ hσ,
    dirichlet_mangoldt_LSeries_eq (a * b) _ hσ, Complex.neg_re, Complex.neg_re, Complex.neg_re] at hh
  linarith

end Ostmann

end OAI
