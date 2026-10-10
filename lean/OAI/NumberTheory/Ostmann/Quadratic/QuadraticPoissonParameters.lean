import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPoissonErrorBound

namespace OAI

/-! # The power-saving parameter specialization in coprime Poisson truncation -/

namespace Ostmann

private theorem cutoff_power {t J : ℝ} (ht : 0 ≤ t) (hJ : 1 ≤ J)
    (htJ : t ≤ 1 / J) (a k : ℕ) : t ^ (a + k) ≤ 1 / J ^ a := by
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have ht1 : t ≤ 1 := htJ.trans ((div_le_one hJ0).mpr hJ)
  calc
    _ = t ^ a * t ^ k := pow_add _ _ _
    _ ≤ (1 / J) ^ a * 1 := mul_le_mul (pow_le_pow_left₀ ht htJ a)
      (pow_le_one₀ ht ht1) (pow_nonneg ht _) (by positivity)
    _ = _ := by rw [div_pow, one_pow, mul_one]

 theorem quadratic_poisson_parameter_budget (a L : ℕ) {X U V J : ℝ}
    (hX : 0 < X) (hU : 0 < U) (hV : 0 < V) (hJ : 1 ≤ J)
    (hUJ : U * J ≤ X) (hJV : X * J ≤ V) (hL : (V / X) ^ 2 ≤ (L : ℝ) + 1) :
    U * (U / X) ^ (a + 3) + X * (X / V) ^ (a + 3) +
      V * (V / X) ^ (a + 3) / ((L : ℝ) + 1) ^ (a + 2) ≤ 3 * X / J ^ a := by
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hsmall : U * (U / X) ^ (a + 3) ≤ X / J ^ a := by
    have hu : U / X ≤ 1 / J := (div_le_div_iff₀ hX hJ0).mpr (by simpa using hUJ)
    have hh := mul_le_mul_of_nonneg_left (cutoff_power (div_nonneg hU.le hX.le) hJ hu a 4) hX.le
    have hp : (U / X) ^ (a + 4) = (U / X) ^ (a + 3) * (U / X) := by
      rw [show a + 4 = (a + 3) + 1 by omega, pow_succ]
    calc
      _ = X * (U / X) ^ (a + 4) := by rw [hp]; field_simp
      _ ≤ X * (1 / J ^ a) := hh
      _ = _ := by ring
  have hlarge : X * (X / V) ^ (a + 3) ≤ X / J ^ a := by
    have hv : X / V ≤ 1 / J := (div_le_div_iff₀ hV hJ0).mpr (by simpa using hJV)
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (cutoff_power (div_nonneg hX.le hV.le) hJ hv a 3) hX.le
  have hmiddle : V * (V / X) ^ (a + 3) / ((L : ℝ) + 1) ^ (a + 2) ≤ X / J ^ a := by
    have hratio : 0 < V / X := div_pos hV hX
    have hbase : J ≤ V / X := (le_div_iff₀ hX).mpr (by simpa only [mul_comm] using hJV)
    calc
      _ ≤ V * (V / X) ^ (a + 3) / ((V / X) ^ 2) ^ (a + 2) :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos (pow_pos hratio 2) (a + 2))
          (pow_le_pow_left₀ (sq_nonneg _) hL (a + 2))
      _ = X / (V / X) ^ a := by
        rw [← pow_mul]
        have he : 2 * (a + 2) = (a + 3) + a + 1 := by omega
        have hp : (V / X) ^ (2 * (a + 2)) =
            (V / X) ^ (a + 3) * (V / X) ^ a * (V / X) := by
          rw [he, pow_add, pow_add, pow_one]
        rw [hp]
        field_simp
      _ ≤ X / J ^ a := div_le_div_of_nonneg_left hX.le (pow_pos hJ0 a)
        (pow_le_pow_left₀ hJ0.le hbase a)
  calc
    _ ≤ X / J ^ a + X / J ^ a + X / J ^ a := add_le_add (add_le_add hsmall hlarge) hmiddle
    _ = _ := by ring

end Ostmann

end OAI
