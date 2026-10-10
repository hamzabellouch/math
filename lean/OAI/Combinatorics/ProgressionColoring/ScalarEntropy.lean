import OAI.Combinatorics.ProgressionColoring.Parameters

namespace OAI

/-!
# Finite scalar entropy of the global row count

The estimates below convert an explicit polynomial count into an entropy bound.
All constants and the threshold depend only on the progression length; no
number of colors or selected prime occurs in these statements.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem log_twice_cutoff_le {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * (cutoff k : ℝ)) ≤ 3 * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hM0 : (0 : ℝ) < cutoff k := by exact_mod_cast cutoff_pos hk1
  have hp : (k : ℝ) ^ (1 / 2 : ℝ) ≤ k := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hk1r (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hM := cutoff_upper hk1
  have htwo : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h ⊢
    exact h
  calc
    Real.log (2 * (cutoff k : ℝ)) ≤ Real.log (4 * (k : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 4 + Real.log k := Real.log_mul (by norm_num) hk0.ne'
    _ ≤ 3 * Real.log k := by rw [hfour]; linarith

/-- Entropy of the coarse direction count. -/
theorem log_direction_count_le {k : ℕ} (hk : 2 ≤ k) {L : ℝ}
    (hL : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ))) :
    Real.log L ≤ 12 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hlog0 : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk1)
  calc
    Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) := hL
    _ ≤ (dimension k : ℝ) ^ 2 * (3 * Real.log k) :=
      mul_le_mul_of_nonneg_left (log_twice_cutoff_le hk) (sq_nonneg _)
    _ ≤ (4 * (k : ℝ) ^ (1 / 5 : ℝ)) * (3 * Real.log k) :=
      mul_le_mul_of_nonneg_right (dimension_sq_upper hk1) (by positivity)
    _ = _ := by ring

/-- Polynomial enlargement of the direction count by the mesh construction. -/
theorem mesh_count_le_polynomial {k : ℕ} (hk : 1 ≤ k) {L F : ℝ}
    (hL : 1 ≤ L) (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k) :
    F ≤ 29 * (k : ℝ) ^ 4 * L := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have hk24 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 :=
    pow_le_pow_right₀ hk1 (by norm_num)
  have hlog : Real.log (k : ℝ) ≤ k :=
    (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hfirst : (k : ℝ) ^ 2 * L ≤ (k : ℝ) ^ 4 * L :=
    mul_le_mul_of_nonneg_right hk24 (by linarith)
  have hsecond : (k : ℝ) ^ 3 * Real.log k ≤ (k : ℝ) ^ 4 * L := by
    calc
      (k : ℝ) ^ 3 * Real.log k ≤ (k : ℝ) ^ 3 * k :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (k : ℝ) ^ 4 := by ring
      _ ≤ (k : ℝ) ^ 4 * L := le_mul_of_one_le_right (by positivity) hL
  linarith

theorem log_mesh_count_le {k : ℕ} (hk : 32 ≤ k) {L F : ℝ}
    (hL : 1 ≤ L) (hFpos : 0 < F)
    (hLlog : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)))
    (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k) :
    Real.log F ≤ 17 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1r
  have hLpos : 0 < L := by linarith
  have hp : 1 ≤ (k : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hk1r (by norm_num)
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1r
  have hlogp : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k :=
    le_mul_of_one_le_left hlog0 hp
  have h29 : Real.log (29 : ℝ) ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 29 ≤ k))
  have hdir := log_direction_count_le (by omega : 2 ≤ k) hLlog
  calc
    Real.log F ≤ Real.log (29 * (k : ℝ) ^ 4 * L) :=
      Real.log_le_log hFpos (mesh_count_le_polynomial hk1 hL hF)
    _ = Real.log 29 + 4 * Real.log k + Real.log L := by
      rw [Real.log_mul (by positivity) hLpos.ne',
        Real.log_mul (by norm_num) (pow_ne_zero 4 hk0.ne'), Real.log_pow]
      norm_num
    _ ≤ 17 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by nlinarith

theorem log_row_base_le {k : ℕ} (hk : 32 ≤ k) {L F : ℝ}
    (hL : 1 ≤ L) (hFone : 1 ≤ F)
    (hLlog : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)))
    (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k) :
    Real.log (3 * (k : ℝ) ^ 2 * F + 1) ≤
      21 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have hFpos : 0 < F := by linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hprod : (1 : ℝ) ≤ (k : ℝ) ^ 2 * F := one_le_mul_of_one_le_of_one_le hk2 hFone
  have hbase : 3 * (k : ℝ) ^ 2 * F + 1 ≤ 4 * (k : ℝ) ^ 2 * F := by nlinarith
  have htwo : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ k))
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h ⊢
    exact h
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hlogp : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k :=
    le_mul_of_one_le_left hlog0 (Real.one_le_rpow hk1 (by norm_num))
  have hmesh := log_mesh_count_le hk hL hFpos hLlog hF
  calc
    Real.log (3 * (k : ℝ) ^ 2 * F + 1) ≤ Real.log (4 * (k : ℝ) ^ 2 * F) :=
      Real.log_le_log (by positivity) hbase
    _ = Real.log 4 + 2 * Real.log k + Real.log F := by
      rw [Real.log_mul (by positivity) hFpos.ne',
        Real.log_mul (by norm_num) (pow_ne_zero 2 hk0.ne'), Real.log_pow]
      norm_num
    _ ≤ 21 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by rw [hfour]; nlinarith

/-- A finite row-count bound gives an explicit entropy constant for every fixed
polynomial exponent `e`; in particular this applies to exponents six and eight. -/
theorem log_global_count_le {k e : ℕ} (hk : 32 ≤ k) {L F T : ℝ}
    (hL : 1 ≤ L) (hFone : 1 ≤ F) (hT : 0 < T)
    (hLlog : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)))
    (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k)
    (hcount : T ≤ (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ e) ^ (2 * dimension k)) :
    Real.log T ≤ (16 + 84 * (e : ℝ)) * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1r
  have hFpos : 0 < F := by linarith
  have hbasepos : 0 < 3 * (k : ℝ) ^ 2 * F + 1 := by positivity
  have htwo : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ k))
  have hsixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h ⊢
    exact h
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1r
  have hp : 1 ≤ (k : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hk1r (by norm_num)
  have hlogp : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k :=
    le_mul_of_one_le_left hlog0 hp
  have hbase := log_row_base_le hk hL hFone hLlog hF
  have hinside : Real.log 16 + (e : ℝ) * Real.log (3 * (k : ℝ) ^ 2 * F + 1) ≤
      (4 + 21 * (e : ℝ)) * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
    have he := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg e : (0 : ℝ) ≤ e)
    rw [hsixteen]
    nlinarith
  have hD : 2 * (dimension k : ℝ) ≤ 4 * (k : ℝ) ^ (1 / 10 : ℝ) := by
    have := dimension_upper hk1
    linarith
  calc
    Real.log T ≤ Real.log ((16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ e) ^ (2 * dimension k)) :=
      Real.log_le_log hT hcount
    _ = (2 * (dimension k : ℝ)) *
        (Real.log 16 + (e : ℝ) * Real.log (3 * (k : ℝ) ^ 2 * F + 1)) := by
      rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero e hbasepos.ne'),
        Real.log_pow]
      push_cast
      ring
    _ ≤ (2 * (dimension k : ℝ)) *
        ((4 + 21 * (e : ℝ)) * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ ≤ (4 * (k : ℝ) ^ (1 / 10 : ℝ)) *
        ((4 + 21 * (e : ℝ)) * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (16 + 84 * (e : ℝ)) *
        ((k : ℝ) ^ (1 / 10 : ℝ) * (k : ℝ) ^ (1 / 5 : ℝ)) * Real.log k := by ring
    _ = _ := by
      rw [← Real.rpow_add hk0]
      norm_num

end QuantitativeVanDerWaerden.Parameters

end

end OAI
