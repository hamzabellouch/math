import OAI.NumberTheory.TwoPointCorrelations.HalaszPhaseIntegral

namespace OAI

/-! A uniform power-sum estimate, using centered cells past the frequency. -/

namespace TwoPointCorrelations

open MeasureTheory Finset

lemma halasz_phase_cells_telescope (t : ℝ) (A N : ℕ) (hA : 1 ≤ A) (hAN : A ≤ N) :
    (∑ n ∈ Ioc A N, ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
      halaszPowerPhase t x) =
      ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
    rw [sum_Ioc_succ_top hAN, ih]
    have he : ((N + 1 : ℕ) : ℝ) - 1 / 2 = (N : ℝ) + 1 / 2 := by push_cast; ring
    rw [he]
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact halasz_power_phase_intervalIntegrable t ((A : ℝ) + 1 / 2)
        ((N : ℝ) + 1 / 2) (by positivity) (by positivity)
    · exact halasz_power_phase_intervalIntegrable t ((N : ℝ) + 1 / 2)
        (((N + 1 : ℕ) : ℝ) + 1 / 2) (by positivity) (by positivity)

lemma halasz_phase_cell_sum_error (t : ℝ) (A N : ℕ) (hA : 1 ≤ A)
    (hAN : A ≤ N) (ht : |t| ≤ (A : ℝ)) :
    ‖(∑ n ∈ Ioc A N, halaszPowerPhase t n) -
      ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤
      (t ^ 2 + |t|) / A := by
  rw [← halasz_phase_cells_telescope t A N hA hAN, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc A N,
        ‖halaszPowerPhase t n -
          ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2), halaszPowerPhase t x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc A N, (t ^ 2 + |t|) / (n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hnA := (mem_Ioc.mp hn).1
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hA.trans hnA.le
      have htn : |t| ≤ (n : ℝ) := ht.trans (by exact_mod_cast hnA.le)
      have hh := halasz_power_phase_cell_integral t n hn1 htn
      rw [intervalIntegral.integral_comp_add_left] at hh
      have he : (n : ℝ) + (-1 / 2) = (n : ℝ) - 1 / 2 := by ring
      rw [he] at hh
      simpa only [norm_sub_rev] using hh
    _ = (t ^ 2 + |t|) * ∑ n ∈ Ioc A N, ((n : ℝ) ^ 2)⁻¹ := by
      simp_rw [div_eq_mul_inv, mul_sum]
    _ ≤ (t ^ 2 + |t|) * ((A : ℝ)⁻¹ - (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by omega : A ≠ 0) hAN) (by positivity)
    _ ≤ (t ^ 2 + |t|) / A := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)

lemma halasz_power_phase_prefix_norm (t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, halaszPowerPhase t n‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖halaszPowerPhase t n‖ := norm_sum_le _ _
    _ = _ := by simp

theorem halasz_power_phase_sum_integral (t : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, halaszPowerPhase t n) -
      ∫ x in (0 : ℝ)..(N : ℝ), halaszPowerPhase t x‖ ≤ 8 * (1 + |t|) := by
  let A : ℕ := ⌈1 + |t|⌉₊
  have hAlo : 1 + |t| ≤ (A : ℝ) := Nat.le_ceil _
  have hAhi : (A : ℝ) < 2 + |t| := by
    have hh : (A : ℝ) < 1 + |t| + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hA1 : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith [abs_nonneg t])
  have hi (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :=
    halasz_power_phase_intervalIntegrable t a b ha hb
  have hb : ∀ M : ℕ,
      ‖(∑ n ∈ Ioc 0 M, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..(M : ℝ), halaszPowerPhase t x‖ ≤ 2 * M := by
    intro M
    calc
      _ ≤ ‖∑ n ∈ Ioc 0 M, halaszPowerPhase t n‖ +
          ‖∫ x in (0 : ℝ)..(M : ℝ), halaszPowerPhase t x‖ := norm_sub_le _ _
      _ ≤ (M : ℝ) + M := add_le_add (halasz_power_phase_prefix_norm t M)
        (by simpa using halasz_power_phase_integral_norm t 0 M)
      _ = _ := by ring
  by_cases hNA : N ≤ A
  · have hNr : (N : ℝ) ≤ A := by exact_mod_cast hNA
    exact (hb N).trans (by linarith [abs_nonneg t])
  · have hAN : A ≤ N := by omega
    have hs := sum_Ioc_consecutive (fun n : ℕ => halaszPowerPhase t n)
      (Nat.zero_le A) hAN
    have hj := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 ((A : ℝ) + 1 / 2) (by norm_num) (by positivity))
      (hi ((A : ℝ) + 1 / 2) ((N : ℝ) + 1 / 2) (by positivity) (by positivity))
    have hk := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 N (by norm_num) (by positivity))
      (hi N ((N : ℝ) + 1 / 2) (by positivity) (by positivity))
    have he : (∑ n ∈ Ioc 0 N, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..(N : ℝ), halaszPowerPhase t x =
        ((∑ n ∈ Ioc 0 A, halaszPowerPhase t n) -
          ∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x) +
        ((∑ n ∈ Ioc A N, halaszPowerPhase t n) -
          ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x) +
        ∫ x in (N : ℝ)..((N : ℝ) + 1 / 2), halaszPowerPhase t x := by
      rw [← hs]
      linear_combination hj - hk
    have hhead : ‖(∑ n ∈ Ioc 0 A, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤ 2 * A + 1 / 2 := by
      calc
        _ ≤ ‖∑ n ∈ Ioc 0 A, halaszPowerPhase t n‖ +
            ‖∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x‖ := norm_sub_le _ _
        _ ≤ (A : ℝ) + ((A : ℝ) + 1 / 2) := add_le_add (halasz_power_phase_prefix_norm t A)
          (by
            have hh := halasz_power_phase_integral_norm t 0 ((A : ℝ) + 1 / 2)
            rw [sub_zero, abs_of_nonneg (by positivity)] at hh
            exact hh)
        _ = _ := by ring
    have htail := halasz_phase_cell_sum_error t A N hA1 hAN (by linarith)
    have hend : ‖∫ x in (N : ℝ)..((N : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤ 1 / 2 := by
      simpa using halasz_power_phase_integral_norm t N ((N : ℝ) + 1 / 2)
    have hratio : (t ^ 2 + |t|) / (A : ℝ) ≤ |t| := by
      apply (div_le_iff₀ (by exact_mod_cast (show 0 < A by omega))).mpr
      have hm := mul_le_mul_of_nonneg_left hAlo (abs_nonneg t)
      nlinarith [sq_abs t]
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hhead htail)) hend)).trans
        (by linarith [abs_nonneg t])

theorem halasz_power_phase_sum (t : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, halaszPowerPhase t n) -
      (N : ℂ) * halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)‖ ≤
        8 * (1 + |t|) := by
  have hset : Icc 1 N = Ioc 0 N := by ext n; simp; omega
  have hh := halasz_power_phase_sum_integral t N
  rw [halasz_power_phase_integral t 0 N (by norm_num) (by positivity)] at hh
  simpa [hset] using hh

theorem halasz_power_phase_sum_real (t x : ℝ) (hx : 0 ≤ x) :
    ‖(∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
      (x : ℂ) * halaszPowerPhase t x / (1 + (-t : ℂ) * Complex.I)‖ ≤
        9 * (1 + |t|) := by
  have hN : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hN' : x - (⌊x⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one x]
  have hj := intervalIntegral.integral_add_adjacent_intervals
    (halasz_power_phase_intervalIntegrable t 0 ⌊x⌋₊ (by norm_num) (by positivity))
    (halasz_power_phase_intervalIntegrable t ⌊x⌋₊ x (by positivity) hx)
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
      ∫ y in (0 : ℝ)..x, halaszPowerPhase t y =
      ((∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
        ∫ y in (0 : ℝ)..(⌊x⌋₊ : ℝ), halaszPowerPhase t y) -
      ∫ y in (⌊x⌋₊ : ℝ)..x, halaszPowerPhase t y := by
    rw [← hj]
    ring
  have hset : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext n; simp; omega
  have hh := halasz_power_phase_sum_integral t ⌊x⌋₊
  rw [← hset] at hh
  have ht : ‖∫ y in (⌊x⌋₊ : ℝ)..x, halaszPowerPhase t y‖ ≤ 1 := by
    apply (halasz_power_phase_integral_norm t ⌊x⌋₊ x).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hN)]
    exact hN'.le
  have h := ((norm_sub_le _ _).trans (add_le_add hh ht)).trans
    (show 8 * (1 + |t|) + 1 ≤ 9 * (1 + |t|) by linarith [abs_nonneg t])
  rw [← he, halasz_power_phase_integral t 0 x (by norm_num) hx] at h
  simpa using h

end TwoPointCorrelations

end OAI
