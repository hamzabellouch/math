import OAI.NumberTheory.Ostmann.ZeroDensity.EventualDensityPrimeBlock

namespace OAI

/-! # Comparing the base parameter with both constructed prime blocks -/

namespace Ostmann

open scoped Classical

theorem primeBlock_log_bounds (P : Finset ℕ) (z : ℕ) (T : ℝ)
    (hz : 2 ≤ z) (hne : P.Nonempty) (hP : P ⊆ logPrimeBand T)
    (hrange : ∀ p ∈ P, z ≤ p ∧ p < 2 * z) :
    T - Real.log 2 < Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ 2 * T := by
  obtain ⟨p, hp⟩ := hne
  have hb := logPrimeBand_mem (hP hp)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hb.1.pos
  have hlow := Real.log_le_log hz0 (show (z : ℝ) ≤ p by exact_mod_cast (hrange p hp).1)
  have hhigh := Real.log_lt_log hp0 (show (p : ℝ) < 2 * z by exact_mod_cast (hrange p hp).2)
  rw [Real.log_mul (by norm_num) hz0.ne'] at hhigh
  constructor <;> linarith [hb.2.1, hb.2.2]

theorem small_primeBlock_log_bounds (T V : ℝ) (z : ℕ) (hT : 0 < T)
    (hVlo : T / 2 ≤ V) (hVhi : V ≤ 2 * T)
    (hU : Real.log 2 ≤ T ^ (1 / 10000000 : ℝ))
    (hz : 0 < z)
    (hlo : T ^ (1 / 10000000 : ℝ) - Real.log 2 < Real.log (z : ℝ))
    (hhi : Real.log (z : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ)) :
    V ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)) ∧
      Real.log (2 * (z : ℝ)) ≤ 8 * V ^ (1 / 10000000 : ℝ) := by
  have hV : 0 < V := by linarith
  have hγ : (0 : ℝ) ≤ 1 / 10000000 := by norm_num
  have h2 : (2 : ℝ) ^ (1 / 10000000 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (show (1 / 10000000 : ℝ) ≤ 1 by norm_num)
  have hv : V ^ (1 / 10000000 : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ) := by
    calc
      _ ≤ (2 * T) ^ (1 / 10000000 : ℝ) := Real.rpow_le_rpow hV.le hVhi hγ
      _ = (2 : ℝ) ^ (1 / 10000000 : ℝ) * T ^ (1 / 10000000 : ℝ) := Real.mul_rpow (by norm_num) hT.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT.le _)
  have ht : T ^ (1 / 10000000 : ℝ) ≤ 2 * V ^ (1 / 10000000 : ℝ) := by
    calc
      _ ≤ (2 * V) ^ (1 / 10000000 : ℝ) := Real.rpow_le_rpow hT.le (by linarith) hγ
      _ = (2 : ℝ) ^ (1 / 10000000 : ℝ) * V ^ (1 / 10000000 : ℝ) := Real.mul_rpow (by norm_num) hV.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hV.le _)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  rw [Real.log_mul (by norm_num) hz0.ne']
  constructor <;> nlinarith [Real.rpow_nonneg hV.le (1 / 10000000 : ℝ)]

end Ostmann

end OAI
