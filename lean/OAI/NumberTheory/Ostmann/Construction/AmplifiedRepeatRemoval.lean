import OAI.NumberTheory.Ostmann.Construction.RepeatRemovalAsymptotics

namespace OAI

/-! # Retaining the amplified moment after deleting all repeated primes -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem repeat_squared_budget (C T K X I I₀ : ℝ) (J k : ℕ)
    (hX : 0 < X) (hI₀ : 0 ≤ I₀)
    (hJ : 0 < J) (hpop : Real.exp T ≤ C * T * J)
    (hXk : X ≤ Real.exp ((k : ℝ) * T)) (hweight : I₀ ≤ C * X)
    (hmoment : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K) ≤ I)
    (hnum : (16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2 ≤
      Real.exp ((4 / 125 : ℝ) * K)) :
    (16 * (k : ℝ) ^ 3 / J) ^ k * I₀ ^ 2 ≤ I ^ 2 := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hA : 0 ≤ 16 * (k : ℝ) ^ 3 / J := by positivity
  have ha : (16 * (k : ℝ) ^ 3 / J) * Real.exp T ≤ 16 * C * T * (k : ℝ) ^ 3 := by
    have hq : Real.exp T / J ≤ C * T := (div_le_iff₀ hJR).mpr hpop
    calc
      _ = (16 * (k : ℝ) ^ 3) * (Real.exp T / J) := by ring
      _ ≤ (16 * (k : ℝ) ^ 3) * (C * T) := by gcongr
      _ = _ := by ring
  have hap := pow_le_pow_left₀ (mul_nonneg hA (Real.exp_nonneg T)) ha k
  rw [mul_pow, ← Real.exp_nat_mul] at hap
  have hsquare := pow_le_pow_left₀ hI₀ hweight 2
  rw [mul_pow] at hsquare
  have hmoment2 := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K)) hmoment 2
  rw [mul_pow, Real.sq_sqrt hX.le, ← Real.exp_nat_mul] at hmoment2
  norm_num only at hmoment2
  have he : (2 : ℝ) * ((2 / 125 : ℝ) * K) = (4 / 125 : ℝ) * K := by ring
  rw [he] at hmoment2
  calc
    _ ≤ (16 * (k : ℝ) ^ 3 / J) ^ k * (C ^ 2 * X ^ 2) := by gcongr
    _ = ((16 * (k : ℝ) ^ 3 / J) ^ k * X) * (C ^ 2 * X) := by ring
    _ ≤ ((16 * (k : ℝ) ^ 3 / J) ^ k * Real.exp ((k : ℝ) * T)) * (C ^ 2 * X) := by gcongr
    _ ≤ (16 * C * T * (k : ℝ) ^ 3) ^ k * (C ^ 2 * X) := by gcongr
    _ = ((16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2) * X := by ring
    _ ≤ Real.exp ((4 / 125 : ℝ) * K) * X := by gcongr
    _ ≤ I ^ 2 := by simpa only [mul_comm] using hmoment2

/-- The actual ternary distinct-prime moment retains at least half of its
positive amplified moment, uniformly for sufficiently large `T`. -/
theorem eventual_amplified_repeat_removal (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ {ι A : Type} [Fintype A] [DecidableEq A]
      (w : ι → ℝ) (y : ι → A → ℝ) (k : ℕ) (K X : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i a, y i a = 0 ∨ y i a = 1 ∨ y i a = -1) →
      Summable w → 0 < k → Even k → k ≤ Fintype.card A →
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → 0 < X →
      Real.exp T ≤ C * T * Fintype.card A → X ≤ Real.exp ((k : ℝ) * T) →
      (∑' i, w i) ≤ C * X →
      Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K) ≤
        (∑' i, w i * ternaryMean (y i) ^ k) →
      (∑' i, w i * ternaryMean (y i) ^ k) / 2 ≤
        (∑' i, w i * ternaryDistinctMean (y i) k) := by
  filter_upwards [eventual_repeat_power_budget C (4 / 125) hC (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with T hnum _hT
  intro ι A _ _ w y k K X hw hy hws hk heven hkA hkU hK hX hpop hXk hweight hmoment
  let I := ∑' i, w i * ternaryMean (y i) ^ k
  let I₀ := ∑' i, w i
  have hI₀ : 0 ≤ I₀ := tsum_nonneg hw
  have hI : 0 ≤ I := le_trans (by positivity) hmoment
  have hJ : 0 < Fintype.card A := lt_of_lt_of_le hk hkA
  have hsq := repeat_squared_budget C T K X I I₀ (Fintype.card A) k
    hX hI₀ hJ hpop hXk hweight hmoment (hnum k K hkU hK)
  have hsmall := repeat_shift_of_squared_budget I I₀ hI hI₀ (Fintype.card A) k hJ hk hsq
  have hshift := moment_small_shift (I ^ (1 / (k : ℝ)))
    ((Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) * I₀ ^ (1 / (k : ℝ)))
    (Real.rpow_nonneg hI _) (by positivity) k hk hsmall
  have hroot : (I ^ (1 / (k : ℝ))) ^ k = I := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI hk.ne'
  rw [hroot] at hshift
  have herr := (weighted_ternary_distinct_moment w y hw hy k hk heven hkA hws).2
  change |(∑' i, w i * ternaryDistinctMean (y i) k) - I| ≤ _ at herr
  have hl := (abs_le.mp herr).1
  change I / 2 ≤ _
  linarith only [hl, hshift]

end Ostmann

end OAI
