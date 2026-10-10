import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSums
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Data.Nat.Factorization.Induction

namespace OAI

/-! The coefficients of zeta times a real quadratic character are
nonnegative, and every positive square contributes at least one. -/

namespace TwoPointCorrelations

open Finset ArithmeticFunction
open scoped Classical ComplexOrder

lemma mrt_character_zeta_coefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ.zetaMul n = ∑ d ∈ n.divisors, χ (d : ZMod q) := by
  rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply]
  apply sum_congr rfl
  intro d hd
  simp only [toArithmeticFunction, coe_mk,
    (Nat.pos_of_mem_divisors hd).ne', ↓reduceIte]


lemma mrt_quadratic_prime_square_coefficient {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (1 : ℂ) ≤ χ.zetaMul (p ^ (2 * k)) := by
  rw [mrt_character_zeta_coefficient, Nat.sum_divisors_prime_pow hp]
  simp only [Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · simp [h]
  · simp only [h, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  · simp [h, neg_one_geom_sum]

theorem mrt_quadratic_square_coefficient {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) (hn : n ≠ 0) :
    (1 : ℂ) ≤ χ.zetaMul (n ^ 2) := by
  have hall : ∀ n : ℕ, n ≠ 0 → (1 : ℂ) ≤ χ.zetaMul (n ^ 2) := by
    apply Nat.recOnPrimeCoprime
    · simp
    · intro p k hp _
      rw [← pow_mul, Nat.mul_comm k 2]
      exact mrt_quadratic_prime_square_coefficient χ hχ hp k
    · intro a b _ _ hab ha hb hne
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne
      have hb0 : b ≠ 0 := right_ne_zero_of_mul hne
      rw [mul_pow, χ.isMultiplicative_zetaMul.map_mul_of_coprime (hab.pow 2 2)]
      exact one_le_mul_of_one_le_of_one_le (ha ha0) (hb hb0)
  exact hall n hn

lemma mrt_quadratic_coefficient_im {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) :
    (χ.zetaMul n).im = 0 :=
  (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg hχ n)).2.symm

lemma mrt_quadratic_coefficient_re_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ (χ.zetaMul n).re :=
  (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg hχ n)).1

lemma mrt_quadratic_square_coefficient_re {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) (hn : n ≠ 0) :
    1 ≤ (χ.zetaMul (n ^ 2)).re :=
  (Complex.le_def.mp (mrt_quadratic_square_coefficient χ hχ n hn)).1


lemma mrt_character_zeta_coefficient_norm {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ.zetaMul n‖ ≤ n := by
  rw [mrt_character_zeta_coefficient]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖χ (d : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := sum_le_sum (fun d _ => χ.norm_le_one _)
    _ = (n.divisors.card : ℝ) := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

end TwoPointCorrelations

end OAI
