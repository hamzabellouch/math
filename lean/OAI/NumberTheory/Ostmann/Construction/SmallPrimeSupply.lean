import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplificationCountBounds
import OAI.NumberTheory.Ostmann.Construction.PrimeBlockLogBounds

namespace OAI

/-! # A populated small-prime block contains enough distinct amplifying primes -/

namespace Ostmann

open Filter
open scoped Classical

theorem eventual_small_prime_population (D : ℝ) (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, ∀ (z : ℕ) (P : Finset ℕ),
      T ^ (1 / 10000000 : ℝ) / 4 ≤ Real.log (z : ℝ) →
      Real.log (z : ℝ) ≤ 8 * T ^ (1 / 10000000 : ℝ) →
      (z : ℝ) ≤ D * Real.log z * P.card → T ≤ (P.card : ℝ) := by
  have hγ : (0 : ℝ) < 1 / 10000000 := by norm_num
  have hnum := eventual_affine_log_le_rpow (1 + 1 / 10000000) (Real.log (8 * D)) (1 / 4)
    (1 / 10000000) (by norm_num) (by norm_num) hγ
  filter_upwards [hnum, eventually_ge_atTop (1 : ℝ)] with T hnum hT z P hlo hhi hpop
  have hTp : 0 < T := by linarith
  have hu : 0 < T ^ (1 / 10000000 : ℝ) := Real.rpow_pos_of_pos hTp _
  have hzpos : 0 < (z : ℝ) := by
    by_contra hn
    have hz0 : z = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg z))
    subst z
    simp only [Nat.cast_zero, Real.log_zero] at hlo
    linarith
  have hnum' : 8 * D * T ^ (1 / 10000000 : ℝ) * T ≤ Real.exp (T ^ (1 / 10000000 : ℝ) / 4) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_mul (by positivity) hTp.ne', Real.log_mul (by positivity) hu.ne',
      Real.log_rpow hTp]
    linarith only [hnum]
  have hnumz : 8 * D * T ^ (1 / 10000000 : ℝ) * T ≤ (z : ℝ) :=
    hnum'.trans ((Real.le_log_iff_exp_le hzpos).mp hlo)
  have hpbound : (z : ℝ) ≤ 8 * D * T ^ (1 / 10000000 : ℝ) * P.card := by
    apply hpop.trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hD.le) (Nat.cast_nonneg P.card)
    nlinarith only [hh]
  exact (mul_le_mul_iff_right₀ (show 0 < 8 * D * T ^ (1 / 10000000 : ℝ) by positivity)).mp
    (by nlinarith only [hnumz, hpbound])

theorem eventual_amplification_prime_count_available (D : ℝ) (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, ∀ (z : ℕ) (P : Finset ℕ), 0 < z →
      T ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)) →
      Real.log (2 * (z : ℝ)) ≤ 8 * T ^ (1 / 10000000 : ℝ) →
      (z : ℝ) ≤ D * Real.log z * P.card → amplificationPrimeCount T z ≤ P.card := by
  have hγ : (0 : ℝ) < 1 / 10000000 := by norm_num
  have hκ : (0 : ℝ) < 9999999 / 10000000 := by norm_num
  filter_upwards [eventual_small_prime_population D hD,
    (tendsto_rpow_atTop hγ).eventually_ge_atTop (4 * Real.log 2),
    (tendsto_rpow_atTop hκ).eventually_ge_atTop 3000000,
    eventually_ge_atTop (1 : ℝ)] with T hpop hU hK hT z P hz hlo hhi hsize
  have hTp : 0 < T := by linarith
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz
  have hlo' : T ^ (1 / 10000000 : ℝ) / 4 ≤ Real.log (z : ℝ) := by
    rw [Real.log_mul (by norm_num) hzpos.ne'] at hlo
    linarith
  have hhi' : Real.log (z : ℝ) ≤ 8 * T ^ (1 / 10000000 : ℝ) := by
    rw [Real.log_mul (by norm_num) hzpos.ne'] at hhi
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hcard := hpop z P hlo' hhi' hsize
  have hcount := (amplificationPrimeCount_bounds T z hTp hlo hhi hK).2.2
  have hpower : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
  exact_mod_cast hcount.trans (hpower.trans hcard)

end Ostmann

end OAI
