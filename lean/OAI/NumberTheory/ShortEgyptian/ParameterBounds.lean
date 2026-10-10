import OAI.NumberTheory.ShortEgyptian.ReciprocalEstimates

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocal_parameter_algebra (r : ℕ) (A F U v b L : ℝ)
    (hA : 1 ≤ A) (hF : 1 ≤ F) (hv : 1 ≤ v) (hU : 0 < U)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hLv : L ≤ 2 * v)
    (hlarge : (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) ≤ U)
    (hbaseLow : 1 ≤ U ^ 3 * b ^ 2) (hbaseHigh : U * b ^ 2 ≤ 1) :
    18 * v ≤ U ∧ (18 * v / U) ^ 2 ≤ F * b / A ∧
      L ^ r * (F * b / A) ≤ (1 / (18 * A * v)) ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hv0 : 0 < v := by linarith
  have hcoef : (18 * A) ^ 4 ≤ (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) := by
    calc
      _ = (18 * A) ^ 4 * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr
        · exact one_le_pow₀ hF
        · exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hU4 : (18 * A) ^ 4 * v ^ 4 ≤ U := by
    apply le_trans _ hlarge
    exact mul_le_mul hcoef (pow_le_pow_right₀ hv (by omega)) (by positivity) (by positivity)
  have h18 : 18 ≤ (18 * A) ^ 4 := by
    have hh := pow_le_pow_right₀ (show 1 ≤ 18 * A by linarith) (show 1 ≤ 4 by norm_num)
    simp only [pow_one] at hh
    linarith
  have hU1 : 18 * v ≤ U := by
    have hp : v ≤ v ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ hv (show 1 ≤ 4 by norm_num)
    exact (mul_le_mul h18 hp hv0.le (by positivity)).trans hU4
  refine ⟨hU1, ?_, ?_⟩
  · have hM : (18 * v) ^ 4 * A ^ 2 ≤ U := by
      have hAA := pow_le_pow_right₀ hA (show 2 ≤ 4 by norm_num)
      have hm := mul_le_mul_of_nonneg_left hAA (show 0 ≤ (18 * v) ^ 4 by positivity)
      have heq : (18 * v) ^ 4 * A ^ 4 = (18 * A) ^ 4 * v ^ 4 := by ring
      rw [heq] at hm
      exact hm.trans hU4
    have hsq1 : ((18 * v / U) ^ 2) ^ 2 ≤ 1 / (A ^ 2 * U ^ 3) := by
      rw [← pow_mul, show 2 * 2 = 4 by norm_num, div_pow]
      apply (div_le_div_iff₀ (by positivity : 0 < U ^ 4) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hM (show 0 ≤ U ^ 3 by positivity)
      nlinarith only [hh]
    have hsq2 : 1 / (A ^ 2 * U ^ 3) ≤ (b / A) ^ 2 := by
      rw [div_pow]
      have hb2 : 1 / U ^ 3 ≤ b ^ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hbaseLow])
      calc
        _ = (1 / U ^ 3) / A ^ 2 := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hb2 (by positivity)
    have hh := (sq_le_sq₀ (sq_nonneg (18 * v / U)) (by positivity : 0 ≤ b / A)).mp (hsq1.trans hsq2)
    apply hh.trans
    have hh' := mul_le_mul_of_nonneg_right hF (show 0 ≤ b / A by positivity)
    simpa only [mul_div_assoc, one_mul] using hh'
  · have hc : F * b / A ≤ F * b := div_le_self (by positivity) hA
    have hterm : L ^ r * (F * b / A) ≤ (2 * v) ^ r * (F * b) :=
      mul_le_mul (pow_le_pow_left₀ hL hLv r) hc (by positivity) (by positivity)
    have hb2 : b ^ 2 ≤ 1 / U := (le_div_iff₀ hU).mpr (by nlinarith only [hbaseHigh])
    have hsq : (L ^ r * (F * b / A)) ^ 2 ≤ ((1 / (18 * A * v)) ^ 2) ^ 2 := by
      calc
        _ ≤ ((2 * v) ^ r * (F * b)) ^ 2 := pow_le_pow_left₀ (by positivity) hterm 2
        _ = ((2 : ℝ) ^ (2 * r) * v ^ (2 * r) * F ^ 2) * b ^ 2 := by
          simp only [mul_pow, ← pow_mul, Nat.mul_comm r 2]
          ring
        _ ≤ ((2 : ℝ) ^ (2 * r) * v ^ (2 * r) * F ^ 2) * (1 / U) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ = ((2 : ℝ) ^ (2 * r) * v ^ (2 * r) * F ^ 2) / U := by ring
        _ ≤ 1 / (18 * A * v) ^ 4 := by
          apply (div_le_div_iff₀ hU (by positivity)).mpr
          calc
            _ = (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) := by
              rw [pow_add]
              ring
            _ ≤ U := hlarge
            _ = 1 * U := by ring
        _ = _ := by rw [← pow_mul, show 2 * 2 = 4 by norm_num, one_div_pow]
    exact (sq_le_sq₀ (by positivity) (sq_nonneg _)).mp hsq

def reciprocalConstantNat (r : ℕ) : ℕ :=
  (18 * 3 ^ (r + 3)) ^ 4 * (r + 2).factorial ^ 2 * 2 ^ (2 * r)

def reciprocalPower (r : ℕ) : ℕ := 2 ^ r * (2 * r + 4)

theorem reciprocalConstant_pos (r : ℕ) : 0 < reciprocalConstantNat r := by
  unfold reciprocalConstantNat
  positivity

theorem reciprocal_phase_order (r : ℕ) (T U Z : ℝ) (p q : ℤ)
    (hT : 1 ≤ T) (hlarge : (reciprocalConstantNat r : ℝ) * T ^ reciprocalPower r ≤ U)
    (hZ : 0 ≤ Z) (hZlo : U ^ (2 * r + 3) ≤ Z ^ 2)
    (hZhi : Z ^ 2 ≤ U ^ (2 * r + 5))
    (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U / T := by
  let A : ℝ := 3 ^ (r + 3)
  let F : ℝ := (r + 2).factorial
  let v : ℝ := T ^ (2 ^ r)
  let L : ℕ := ⌈v⌉₊
  let b : ℝ := Z / U ^ (r + 3)
  have hT0 : 0 < T := by linarith
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hF : 1 ≤ F := by
    have h : 1 ≤ (r + 2).factorial := Nat.factorial_pos (r + 2)
    dsimp only [F]
    exact_mod_cast h
  have hv : 1 ≤ v := one_le_pow₀ hT
  have hv0 : 0 < v := by linarith
  have hC0 : (0 : ℝ) < reciprocalConstantNat r := by exact_mod_cast reciprocalConstant_pos r
  have hU : 0 < U := lt_of_lt_of_le (mul_pos hC0 (by positivity)) hlarge
  have hL : 1 ≤ L := Nat.ceil_pos.mpr hv0
  have hLv : (L : ℝ) ≤ 2 * v := by
    have hh := Nat.ceil_lt_add_one hv0.le
    change (⌈v⌉₊ : ℝ) ≤ _
    linarith
  have hbaseLow : 1 ≤ U ^ 3 * b ^ 2 := by
    have heq : U ^ 3 * b ^ 2 = Z ^ 2 / U ^ (2 * r + 3) := by
      dsimp only [b]
      rw [div_pow, ← pow_mul, show (r + 3) * 2 = 3 + (2 * r + 3) by omega, pow_add]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity)).mpr hZlo
  have hbaseHigh : U * b ^ 2 ≤ 1 := by
    have heq : U * b ^ 2 = Z ^ 2 / U ^ (2 * r + 5) := by
      dsimp only [b]
      rw [div_pow, ← pow_mul, show (r + 3) * 2 = 1 + (2 * r + 5) by omega, pow_add, pow_one]
      field_simp
    rw [heq]
    exact (div_le_one (by positivity)).mpr hZhi
  have hlarge' : (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) ≤ U := by
    simpa only [A, F, v, ← pow_mul, reciprocalPower, reciprocalConstantNat,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hlarge
  obtain ⟨hU1, hlo, hup⟩ := reciprocal_parameter_algebra r A F U v b L
    hA hF hv hU (by dsimp [b]; positivity) (by positivity) hLv hlarge' hbaseLow hbaseHigh
  have hUone : 1 ≤ U := by nlinarith
  have hfunc : F * b / A = Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)) := by
    dsimp only [F, b, A]
    rw [one_div_pow, mul_pow]
    field_simp
  have hepow : (1 / T) ^ (2 ^ r) = 1 / v := one_div_pow T (2 ^ r)
  have heps : 0 < (1 : ℝ) / T := by positivity
  have heps1 : (1 : ℝ) / T ≤ 1 := (div_le_one hT0).mpr hT
  have hLin : 1 / (L : ℝ) ≤ (1 / T) ^ (2 ^ r) := by
    rw [hepow]
    exact one_div_le_one_div_of_le hv0 (Nat.le_ceil v)
  have hconstant : 18 ≤ U * (1 / T) ^ (2 ^ r) := by
    rw [hepow, mul_one_div]
    exact (le_div_iff₀ hv0).mpr hU1
  have hlo' : (18 / (U * (1 / T) ^ (2 ^ r))) ^ 2 ≤
      Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)) := by
    rw [← hfunc, hepow]
    convert hlo using 1; field_simp
  have hup' : (L : ℝ) ^ r * (Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))) ≤
      ((1 / T) ^ (2 ^ r) / (18 * (3 : ℝ) ^ (r + 3))) ^ 2 := by
    rw [← hfunc, hepow]
    convert hup using 1; field_simp; rfl
  have hh := reciprocal_phase_parameter_bound r L Z U (1 / T) p q hL hUone
    (by nlinarith) hZ hp hq heps heps1 hLin hconstant hlo' hup'
  simpa only [mul_one_div] using hh

theorem reciprocalConstant_mono : Monotone reciprocalConstantNat := by
  intro r s hrs
  unfold reciprocalConstantNat
  gcongr

theorem reciprocalPower_mono : Monotone reciprocalPower := by
  intro r s hrs
  unfold reciprocalPower
  gcongr

theorem reciprocal_phase_power_bound (B : ℕ) (T U Z : ℝ) (p q : ℤ)
    (hB : 4 ≤ B) (hT : 1 ≤ T)
    (hlarge : (reciprocalConstantNat B : ℝ) * T ^ reciprocalPower B ≤ U)
    (hZlo : U ^ 4 ≤ |Z|) (hZhi : |Z| ≤ U ^ B)
    (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U / T := by
  have hC : (1 : ℝ) ≤ reciprocalConstantNat B := by
    exact_mod_cast reciprocalConstant_pos B
  have hU : 1 ≤ U := le_trans (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hT)) hlarge
  have hlow : U ^ 8 ≤ |Z| ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ U ^ 4) hZlo 2
  have hhigh : |Z| ^ 2 ≤ U ^ (2 * B) := by
    simpa only [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (abs_nonneg Z) hZhi 2
  have hex : ∃ r : ℕ, 2 ≤ r ∧ |Z| ^ 2 ≤ U ^ (2 * r + 5) := by
    exact ⟨B, by omega, hhigh.trans (pow_le_pow_right₀ hU (by omega))⟩
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  change 2 ≤ r ∧ |Z| ^ 2 ≤ U ^ (2 * r + 5) at hr
  have hrB : r ≤ B := Nat.find_min' hex ⟨by omega, hhigh.trans (pow_le_pow_right₀ hU (by omega))⟩
  have hrlo : U ^ (2 * r + 3) ≤ |Z| ^ 2 := by
    by_cases heq : r = 2
    · rw [heq]
      exact (pow_le_pow_right₀ hU (by norm_num : 2 * 2 + 3 ≤ 8)).trans hlow
    · have hprev := Nat.find_min hex (show r - 1 < r by omega)
      have hnot : ¬ |Z| ^ 2 ≤ U ^ (2 * (r - 1) + 5) := fun hh => hprev ⟨by omega, hh⟩
      have he : 2 * (r - 1) + 5 = 2 * r + 3 := by omega
      rw [he] at hnot
      exact (lt_of_not_ge hnot).le
  have hlarge' : (reciprocalConstantNat r : ℝ) * T ^ reciprocalPower r ≤ U := by
    apply le_trans _ hlarge
    gcongr
    · exact_mod_cast reciprocalConstant_mono hrB
    · exact reciprocalPower_mono hrB
  have hh := reciprocal_phase_order r T U |Z| p q hT hlarge' (abs_nonneg Z) hrlo hr.2 hp hq
  rcases le_total 0 Z with hZ | hZ
  · simpa only [abs_of_nonneg hZ] using hh
  · rw [abs_of_nonpos hZ] at hh
    simpa only [neg_div, phase_neg, ← map_sum, Complex.norm_conj] using hh

end ShortEgyptian

end OAI
