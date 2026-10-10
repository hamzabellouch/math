import OAI.NumberTheory.ShortEgyptian.ResidueDiscrepancy

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_reciprocals_band (s : Finset ℕ) (R : ℝ) (hR : 1 < R)
    (hs : ∀ p ∈ s, p.Prime ∧ R ≤ p ∧ (p : ℝ) ≤ 2 * R) :
    ∑ p ∈ s, (1 : ℝ) / p ≤ 2 * Real.log 4 / Real.log R := by
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have hl : 0 < Real.log R := Real.log_pos hR
  have hsub : s ⊆ Nat.primesLE ⌊2 * R⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs p hp).2.2, (hs p hp).1⟩
  have hsum : ∑ p ∈ s, Real.log p ≤ Real.log 4 * (2 * R) := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE ⌊2 * R⌋₊, Real.log p :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Chebyshev.theta (2 * R) := (Chebyshev.theta_eq_sum_primesLE _).symm
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (by positivity)
  calc
    _ ≤ ∑ p ∈ s, Real.log p / (R * Real.log R) := by
      apply sum_le_sum
      intro p hp
      have hpp : 0 < (p : ℝ) := lt_of_lt_of_le hRp (hs p hp).2.1
      apply (div_le_div_iff₀ hpp (mul_pos hRp hl)).mpr
      have hlog := Real.log_le_log hRp (hs p hp).2.1
      nlinarith [mul_le_mul_of_nonneg_left hlog hpp.le,
        mul_le_mul_of_nonneg_right (hs p hp).2.1 hl.le]
    _ = (∑ p ∈ s, Real.log p) / (R * Real.log R) := (sum_div _ _ _).symm
    _ ≤ (Real.log 4 * (2 * R)) / (R * Real.log R) := by gcongr
    _ = _ := by field_simp

theorem prime_reciprocals_dyadic (K : ℕ) :
    ∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p ≤ 4 * (1 + (harmonic K : ℝ)) := by
  induction K with
  | zero =>
    have h : Nat.primesLE 2 = {2} := by decide
    norm_num [h]
  | succ K ih =>
    let s := (Nat.primesLE (2 ^ (K + 1 + 1))).filter fun p => 2 ^ (K + 1) < p
    have hsplit :
        ∑ p ∈ Nat.primesLE (2 ^ (K + 1 + 1)), (1 : ℝ) / p =
        (∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p) + ∑ p ∈ s, (1 : ℝ) / p := by
      rw [← sum_filter_add_sum_filter_not _ (fun p => p ≤ 2 ^ (K + 1))]
      congr 1
      · congr 1
        ext p
        simp only [mem_filter, Nat.mem_primesLE]
        have hp : 2 ^ (K + 1) ≤ 2 ^ (K + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1.trans hp, h2⟩, h1⟩
      · simp [s]
    have hb := prime_reciprocals_band s ((2 : ℝ) ^ (K + 1))
      (by exact one_lt_pow₀ (by norm_num) (by omega)) (by
        intro p hp
        obtain ⟨hp, hp'⟩ := mem_filter.mp hp
        obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
        refine ⟨hprime, ?_, ?_⟩
        · exact_mod_cast hp'.le
        · have hle' : (p : ℝ) ≤ (2 : ℝ) ^ (K + 1 + 1) := by exact_mod_cast hle
          simpa [pow_succ, mul_comm] using hle')
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow 2 2 using 1
      norm_num
    rw [Real.log_pow, hlog4] at hb
    have hb' : ∑ p ∈ s, (1 : ℝ) / p ≤ 4 / (K + 1 : ℕ) := by
      convert hb using 1
      field_simp
      norm_num
    rw [hsplit, harmonic_succ]
    push_cast
    push_cast at hb'
    rw [div_eq_mul_inv] at hb'
    linarith

theorem prime_reciprocals_bound (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      8 + 4 * Real.log (1 + Real.log T / Real.log 2) := by
  let K := Nat.log 2 T
  have hK : 0 < K := Nat.log_pos (by norm_num) hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hpower : (2 : ℝ) ^ K ≤ T := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : T ≠ 0)
  have hlog : (K : ℝ) ≤ Real.log T / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    simpa [Real.log_pow] using Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ K) hpower
  have hharm := harmonic_le_one_add_log K
  have hlog' : Real.log K ≤ Real.log (1 + Real.log T / Real.log 2) := by
    apply Real.log_le_log (by exact_mod_cast hK)
    linarith
  calc
    _ ≤ ∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p :=
      sum_le_sum_of_subset_of_nonneg
        (Nat.primesLE_mono (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) T).le)
        (fun _ _ _ => by positivity)
    _ ≤ 4 * (1 + (harmonic K : ℝ)) := prime_reciprocals_dyadic K
    _ ≤ _ := by linarith

end ShortEgyptian

end OAI
