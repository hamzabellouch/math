import Mathlib

namespace OAI


noncomputable section

namespace Problem355.PrimeParameters

theorem exists_base_prime (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
      B ≤ 200 * k ^ 2 * r ^ 30 := by
  obtain ⟨B, hB, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (100 * k ^ 2 * r ^ 30) (by positivity)
  refine ⟨B, hB, hlo, ?_⟩
  nlinarith only [hhi]

theorem exists_base_prime_le_pow (k r : ℕ) (hk : 0 < k)
    (hr : 200 * k ^ 2 ≤ r) :
    ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
      B ≤ 200 * k ^ 2 * r ^ 30 ∧ B ≤ r ^ 31 := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  obtain ⟨B, hB, hlo, hhi⟩ := exists_base_prime k r hk hr0
  refine ⟨B, hB, hlo, hhi, hhi.trans ?_⟩
  calc
    200 * k ^ 2 * r ^ 30 ≤ r * r ^ 30 := Nat.mul_le_mul_right _ hr
    _ = r ^ 31 := by ring

theorem exists_auxiliary_prime (h : ℕ) (hh : 2 ≤ h) :
    ∃ q : ℕ, q.Prime ∧ h ^ 100 < q ∧ q ≤ 2 * h ^ 100 ∧
      q ≤ h ^ 101 ∧ h.Coprime q := by
  have hh0 : 0 < h := by omega
  obtain ⟨q, hq, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (h ^ 100) (by positivity)
  have hhpow : h ≤ h ^ 100 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < h) (by norm_num : 1 ≤ 100))
  refine ⟨q, hq, hlo, hhi, ?_, ?_⟩
  · calc
      q ≤ 2 * h ^ 100 := hhi
      _ ≤ h * h ^ 100 := Nat.mul_le_mul_right _ hh
      _ = h ^ 101 := by ring
  · exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hh0 (hhpow.trans_lt hlo))).symm

theorem auxiliary_prime_large (h q : ℕ) (hh : 2 ≤ h) (hq : h ^ 100 < q) :
    2000 * (h ^ 2) ^ 2 ≤ q := by
  have hpow : 2000 ≤ h ^ 96 := by
    calc
      2000 ≤ 2 ^ 96 := by norm_num
      _ ≤ h ^ 96 := Nat.pow_le_pow_left hh 96
  have hprod : 2000 * h ^ 4 ≤ h ^ 96 * h ^ 4 :=
    Nat.mul_le_mul_right _ hpow
  have heq : h ^ 96 * h ^ 4 = h ^ 100 := by ring
  have heq' : (h ^ 2) ^ 2 = h ^ 4 := by ring
  rw [heq']
  exact (hprod.trans_eq heq).trans hq.le

theorem exists_prime_parameters (k r : ℕ) (hk : 0 < k)
    (hr : 200 * k ^ 2 ≤ r) :
    ∃ B q : ℕ, B.Prime ∧ q.Prime ∧
      100 * k ^ 2 * r ^ 30 < B ∧ B ≤ 200 * k ^ 2 * r ^ 30 ∧
      B ≤ r ^ 31 ∧ (B ^ k) ^ 100 < q ∧ q ≤ 2 * (B ^ k) ^ 100 ∧
      q ≤ (B ^ k) ^ 101 ∧ (B ^ k).Coprime q ∧
      2000 * ((B ^ k) ^ 2) ^ 2 ≤ q := by
  obtain ⟨B, hB, hlo, hhi, hpoly⟩ := exists_base_prime_le_pow k r hk hr
  have hBk : 2 ≤ B ^ k := by
    calc
      2 ≤ B := hB.two_le
      _ ≤ B ^ k := by
        simpa using Nat.pow_le_pow_right hB.pos hk
  obtain ⟨q, hq, hqlo, hqhi, hqpoly, hcop⟩ := exists_auxiliary_prime (B ^ k) hBk
  exact ⟨B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop,
    auxiliary_prime_large (B ^ k) q hBk hqlo⟩

theorem digit_moment_parameter_le_half (k r B : ℕ) (hk : 0 < k)
    (hr : 400 * k ^ 2 ≤ r) (hB : B ≤ 200 * k ^ 2 * r ^ 30) :
    (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hrpos
  have hc : (400 : ℝ) * (k : ℝ) ^ 2 ≤ (r : ℝ) ^ 6 := by
    calc
      (400 : ℝ) * (k : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hr
      _ ≤ (r : ℝ) ^ 6 := by
        simpa using pow_le_pow_right₀ hr1 (by norm_num : 1 ≤ 6)
  have hb : (B : ℝ) ≤ 200 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30 := by exact_mod_cast hB
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (r : ℝ) ^ 30)
  have heq : (r : ℝ) ^ 6 * (r : ℝ) ^ 30 = (r : ℝ) ^ 36 := by ring
  rw [heq] at hm
  have hid : (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 =
      (B : ℝ) / (r : ℝ) ^ 36 := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (by positivity : 0 < (r : ℝ) ^ 36)).2
  nlinarith only [hb, hm]

theorem exists_base_for_sampling (k r : ℕ) (hk : 0 < k)
    (hr : 400 * k ^ 2 ≤ r) :
    ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
      B ≤ 200 * k ^ 2 * r ^ 30 ∧ B ≤ r ^ 31 ∧ r ^ 10 < B ∧
      (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hr' : 200 * k ^ 2 ≤ r := by nlinarith only [hr]
  obtain ⟨B, hB, hlo, hhi, hpoly⟩ := exists_base_prime_le_pow k r hk hr'
  refine ⟨B, hB, hlo, hhi, hpoly, ?_, digit_moment_parameter_le_half k r B hk hr hhi⟩
  apply lt_of_le_of_lt _ hlo
  calc
    r ^ 10 ≤ r ^ 30 := Nat.pow_le_pow_right hrpos (by norm_num)
    _ ≤ 100 * k ^ 2 * r ^ 30 := by
      have hc : 1 ≤ 100 * k ^ 2 := by
        have hpos : 0 < 100 * k ^ 2 := by positivity
        omega
      simpa using Nat.mul_le_mul_right (r ^ 30) hc

theorem exists_odd_prime_sequence :
    ∃ r : ℕ → ℕ, Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ j, (r j).Prime ∧ Odd (r j) ∧ j ≤ r j := by
  choose r hr using fun j : ℕ => Nat.exists_infinite_primes (max j 3)
  refine ⟨r, ?_, ?_⟩
  · exact Filter.tendsto_atTop_mono (fun j => (Nat.le_max_left j 3).trans (hr j).1)
      Filter.tendsto_id
  · intro j
    have hthree : 3 ≤ r j := (Nat.le_max_right j 3).trans (hr j).1
    exact ⟨(hr j).2, (hr j).2.odd_of_ne_two (by omega),
      (Nat.le_max_left j 3).trans (hr j).1⟩

end Problem355.PrimeParameters

end

end OAI
