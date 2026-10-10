import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem pow_mul_lt_sq_of_popular_lower
    (K s t : ℝ) (j : ℕ) (hK : 0 < K) (hs : 0 < s)
    (ht : s / (2 * K) ≤ t) (hlarge : 4 * K ^ (j + 2) < s) :
    K ^ j * s < t ^ 2 := by
  have hden : 0 < 2 * K := mul_pos (by norm_num) hK
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hsq : s ^ 2 ≤ (2 * K * t) ^ 2 := pow_le_pow_left₀ hs.le hst 2
  apply (mul_lt_mul_iff_left₀ (pow_pos hden 2)).mp
  calc
    (K ^ j * s) * (2 * K) ^ 2 = 4 * K ^ (j + 2) * s := by
      rw [pow_add]
      ring
    _ < s ^ 2 := by nlinarith [mul_lt_mul_of_pos_right hlarge hs]
    _ ≤ t ^ 2 * (2 * K) ^ 2 := by nlinarith only [hsq]

theorem noapprox_threshold_numerics
    (K s t : ℝ) (hK : 2 ≤ K) (ht : s / (2 * K) ≤ t)
    (hlarge : 4 * K ^ 127942 < s) :
    0 < s ∧ 2 < t ∧ K ^ 127940 * s < t ^ 2 ∧
      2 * (K ^ 527 * s) < t ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hKone : 1 ≤ K := le_trans (by norm_num) hK
  have hs : 0 < s := lt_trans (mul_pos (by norm_num) (pow_pos hKpos _)) hlarge
  have hden : 0 < 2 * K := mul_pos (by norm_num) hKpos
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hKpow : K ≤ K ^ 127942 := le_self_pow₀ hKone (by norm_num)
  have htlarge : 2 < t := by
    apply (mul_lt_mul_iff_right₀ hden).mp
    nlinarith only [hlarge, hKpow, hst]
  have hlong : K ^ 127940 * s < t ^ 2 :=
    pow_mul_lt_sq_of_popular_lower K s t 127940 hKpos hs ht hlarge
  have hpow : 2 * K ^ 527 ≤ K ^ 127940 := by
    calc
      2 * K ^ 527 ≤ K * K ^ 527 :=
        mul_le_mul_of_nonneg_right hK (pow_nonneg hKpos.le _)
      _ = K ^ 528 := (pow_succ' K 527).symm
      _ ≤ K ^ 127940 := pow_le_pow_right₀ hKone (by norm_num)
  refine ⟨hs, htlarge, hlong, ?_⟩
  calc
    2 * (K ^ 527 * s) = (2 * K ^ 527) * s := by ring
    _ ≤ K ^ 127940 * s := mul_le_mul_of_nonneg_right hpow hs.le
    _ < t ^ 2 := hlong

theorem cube_lt_of_popular_lower
    (K s t q : ℝ) (hK : 0 < K) (hs : 0 ≤ s)
    (ht : s / (2 * K) ≤ t) (hlarge : 8 * K ^ 3 * q < s ^ 3) :
    q < t ^ 3 := by
  have hden : 0 < 2 * K := mul_pos (by norm_num) hK
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hcube : s ^ 3 ≤ (2 * K * t) ^ 3 := pow_le_pow_left₀ hs hst 3
  apply (mul_lt_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ) < 8)
    (pow_pos hK 3))).mp
  calc
    8 * K ^ 3 * q < s ^ 3 := hlarge
    _ ≤ (2 * K * t) ^ 3 := hcube
    _ = 8 * K ^ 3 * t ^ 3 := by ring

end RyserCoveringCounterexample.Incidence

end OAI
