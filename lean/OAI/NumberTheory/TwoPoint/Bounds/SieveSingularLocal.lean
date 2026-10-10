import OAI.NumberTheory.TwoPoint.Bounds.SieveEulerLower

namespace OAI

/-! An elementary square-root divisor majorant for the sieve singular factor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sieve_euler_factor_eq {p : ℕ} (hp : p.Prime) :
    sieveEulerFactor p = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold sieveEulerFactor
  field_simp

lemma sieve_euler_factor_le_two {p : ℕ} (hp : p.Prime) : sieveEulerFactor p ≤ 2 := by
  rw [sieve_euler_factor_eq hp]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
  linarith

lemma sieve_euler_square_le {p : ℕ} (hp : p.Prime) :
    sieveEulerFactor p ^ 2 ≤ 1 + 6 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  rw [sieve_euler_factor_eq hp, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hp1)).mpr
  apply (mul_le_mul_iff_right₀ hp0).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hpR) (show (0 : ℝ) ≤ 4 * p - 3 by linarith)]

lemma sieve_euler_square_sqrt {p : ℕ} (hp : p.Prime) (hp36 : 36 ≤ p) :
    sieveEulerFactor p ^ 2 ≤ 1 + 1 / Real.sqrt (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs2 := Real.sq_sqrt hp0.le
  have hs6 : (6 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have : (36 : ℝ) ≤ p := by exact_mod_cast hp36
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  have he : 6 / (p : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by
    apply (div_le_div_iff₀ hp0 hs0).mpr
    nlinarith
  exact (sieve_euler_square_le hp).trans (by linarith)

lemma sieve_singular_square_product (N : ℕ) :
    sieveSingularFactor N ^ 2 ≤
      (4 : ℝ) ^ 36 * (∏ p ∈ N.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) := by
  let P := N.primeFactors
  let S := P.filter (fun p => p < 36)
  have hsmall : S.card ≤ 36 := by
    have hs : S ⊆ range 36 := by
      intro p hp
      exact mem_range.mpr (mem_filter.mp hp).2
    simpa using card_le_card hs
  have hfac (p : ℕ) (hp : p ∈ P) :
      sieveEulerFactor p ^ 2 ≤ (if p < 36 then 4 else 1) * (1 + 1 / Real.sqrt (p : ℝ)) := by
    have hprime := (Nat.mem_primeFactors.mp hp).1
    by_cases h36 : p < 36
    · rw [ite_eq_left h36]
      have he := pow_le_pow_left₀ (sieve_euler_factor_pos hprime).le (sieve_euler_factor_le_two hprime) 2
      have : 0 ≤ 1 / Real.sqrt (p : ℝ) := by positivity
      nlinarith
    · rw [ite_eq_right h36, one_mul]
      exact sieve_euler_square_sqrt hprime (by omega)
  have hp := prod_le_prod₀ (fun p _ => sq_nonneg (sieveEulerFactor p)) hfac
  have hconst : (∏ p ∈ P, (if p < 36 then (4 : ℝ) else 1)) ≤ (4 : ℝ) ^ 36 := by
    have he : (∏ p ∈ P, (if p < 36 then (4 : ℝ) else 1)) = (4 : ℝ) ^ S.card := by
      rw [← prod_filter]
      simp only [S, prod_const]
    rw [he]
    exact pow_le_pow_right₀ (by norm_num) hsmall
  rw [prod_mul_distrib, prod_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right hconst
    (prod_nonneg (fun p _ => by positivity)))

end TwoPointCorrelations

end OAI
