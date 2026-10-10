import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctAdaptiveBound

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem normalize_adaptive_power_bound {P S J C : ℝ} (hJ : 0 < J)
    {k : ℕ} (hk : 2 ≤ k)
    (hb : |P - S ^ k| ≤ C * J * (S + (k : ℝ) * Real.sqrt J) ^ (k - 2)) :
    |P / J ^ k - (S / J) ^ k| ≤
      (C / J) * (S / J + (k : ℝ) / Real.sqrt J) ^ (k - 2) := by
  have hJne := hJ.ne'
  have hspos : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJ
  have hsq := Real.sq_sqrt hJ.le
  have hn : k = (k - 2) + 2 := by omega
  have hnormal : (S + (k : ℝ) * Real.sqrt J) / J = S / J + (k : ℝ) / Real.sqrt J := by
    field_simp
    nlinarith [hsq]
  have hscale : C * J * (S + (k : ℝ) * Real.sqrt J) ^ (k - 2) / J ^ k =
      (C / J) * ((S + (k : ℝ) * Real.sqrt J) / J) ^ (k - 2) := by
    rw [div_pow]
    have hpow : J ^ k = J ^ (k - 2) * J ^ 2 := by rw [← pow_add, ← hn]
    rw [hpow, pow_two]
    field_simp
  rw [div_pow, ← sub_div, abs_div, abs_of_pos (pow_pos hJ _)]
  calc
    |P - S ^ k| / J ^ k ≤
        C * J * (S + (k : ℝ) * Real.sqrt J) ^ (k - 2) / J ^ k :=
      div_le_div_of_nonneg_right hb (pow_nonneg hJ.le _)
    _ = _ := by rw [hscale, hnormal]

theorem paired_series_normalized_adaptive_error_bound {S m J k : ℕ}
    (hS : S ≤ J) (hm : m ≤ J) (hJ : 0 < J) (hk : 2 ≤ k) :
    |((k.factorial : ℝ) *
        (∑ j ∈ Finset.range (m + 1),
          if 2 * j ≤ k then (-1 : ℝ) ^ j * (m.choose j : ℝ) * (S.choose (k - 2 * j) : ℝ)
          else 0)) / (J : ℝ) ^ k - ((S : ℝ) / J) ^ k| ≤
      (((k : ℝ) + 1) * (k : ℝ) ^ 2 / J) *
        ((S : ℝ) / J + (k : ℝ) / Real.sqrt (J : ℝ)) ^ (k - 2) := by
  apply normalize_adaptive_power_bound (by exact_mod_cast hJ) hk
  exact paired_series_adaptive_error_bound hS hm hk

end Ostmann.QuadraticCenter

end OAI
