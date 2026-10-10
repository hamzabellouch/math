import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWideRows
import OAI.NumberTheory.Ostmann.Preliminaries.SummandSizePrimeBand

namespace OAI

/-! # Enough actual dilation primes from the proved principal prime estimate -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

theorem quadratic_dilation_primes_sqrt :
    ∀ᶠ Q : ℕ in atTop, 2 ≤ Q ∧ Real.sqrt Q ≤ (sizePrimeBand Q).card := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hlog)
  filter_upwards [sizePrimeBand_eventual_bounds, eventually_ge_atTop A] with Q hband hQA
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hh := hA (2 * Q) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * (Q : ℝ)) (1 / 2 : ℝ))] at hh
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)] at hh
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsmall : 4 * Real.log (2 * (Q : ℝ)) ≤ Real.sqrt Q := by
    have hm := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg (Q : ℝ))
    nlinarith [le_abs_self (Real.log (2 * (Q : ℝ)))]
  have hden : 0 < 4 * Real.log (2 * (Q : ℝ)) := by
    apply mul_pos (by norm_num)
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hband.1
    linarith
  refine ⟨hband.1, le_trans ?_ hband.2.1⟩
  apply (le_div_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg (Q : ℝ))
  simpa only [Real.mul_self_sqrt hQ.le] using hm

theorem quadratic_dilation_prime_supply (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ X Q : ℕ, 0 < X →
      C * (X : ℝ) ^ δ ≤ Q →
        2 ≤ Q ∧ 6 * Nat.log 2 X ≤ (sizePrimeBand Q).card := by
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp quadratic_dilation_primes_sqrt
  let A := 1 + ((δ / 2) * Real.log 2)⁻¹
  let C := (Q₀ : ℝ) + 2 + (6 * A) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (6 * A), Nat.cast_nonneg (α := ℝ) Q₀]
  refine ⟨C, hC, ?_⟩
  intro X Q hX hCQ
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hp : 1 ≤ (X : ℝ) ^ δ := Real.one_le_rpow hX₁ hδ.le
  have hQreal : (Q₀ : ℝ) ≤ Q := by
    have : (Q₀ : ℝ) ≤ C := by dsimp [C]; nlinarith [sq_nonneg (6 * A)]
    have hle := le_mul_of_one_le_right (by linarith : 0 ≤ C) hp
    exact this.trans (hle.trans hCQ)
  have hband := hQ₀ Q (by exact_mod_cast hQreal)
  have hlog : (Nat.log 2 X : ℝ) ≤ A * (X : ℝ) ^ (δ / 2) := by
    have hh := quadratic_dyadic_count_bound (δ / 2) (by positivity) X hX
    dsimp [A]
    push_cast at hh
    linarith
  have hroot : 6 * A * (X : ℝ) ^ (δ / 2) ≤ Real.sqrt Q := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg Q)).mpr
    have hCbig : (6 * A) ^ 2 ≤ C := by dsimp [C]; nlinarith [Nat.cast_nonneg (α := ℝ) Q₀]
    have he : ((X : ℝ) ^ (δ / 2)) ^ 2 = (X : ℝ) ^ δ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
      congr 1
      ring
    rw [mul_pow, mul_pow, he]
    have hh := mul_le_mul_of_nonneg_right hCbig (Real.rpow_nonneg hXp.le δ)
    nlinarith
  refine ⟨hband.1, ?_⟩
  have hh := (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 6)).trans
    (by simpa only [mul_assoc] using hroot.trans hband.2)
  exact_mod_cast hh

end Ostmann

end OAI
