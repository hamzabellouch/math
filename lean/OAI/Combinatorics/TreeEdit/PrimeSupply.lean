import OAI.Combinatorics.TreeEdit.Model

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace PrimeSupply
open Filter

lemma primeCounting_le (n : ℕ) : n.primeCounting ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hh : n.primesLE ⊆ Finset.Icc 1 n := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_lt.le, (Nat.mem_primesLE.mp hp).1⟩
  simpa using Finset.card_le_card hh

lemma eventually_pi_power (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ k : ℕ in atTop, 2 * k ^ a ≤ (k ^ (a + 1)).primeCounting := by
  have ht : Tendsto (fun k : ℕ => Real.log (k : ℝ) / k) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually_lt_const (show (0 : ℝ) < 1 / (8 * (a + 1)) by positivity)
  filter_upwards [hev, eventually_ge_atTop (8 * (a + 2))] with k hk hlarge
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hka : (8 : ℝ) * (a + 2) ≤ k := by exact_mod_cast hlarge
  have hsmall : ((a : ℝ) + 1) * Real.log k ≤ (k : ℝ) / 8 := by
    have hh := (div_lt_iff₀ hkp).mp hk
    have hann : (0 : ℝ) < 8 * (a + 1) := by positivity
    have hh' := (lt_div_iff₀ hann).mp (show Real.log k < (k : ℝ) / (8 * (a + 1)) by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh)
    linarith
  have hkn : (1 : ℝ) ≤ k := by linarith
  have hn : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ (a + 1) := pow_le_pow_right₀ hkn (by omega)
  have hn1 : (1 : ℝ) ≤ (k : ℝ) ^ (a + 1) := one_le_pow₀ hkn
  have hlog : Real.log ((k : ℝ) ^ (a + 1) + 1) ≤ (k : ℝ) ^ (a + 1) / 4 := by
    calc
      _ ≤ Real.log (2 * (k : ℝ) ^ (a + 1)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + ((a : ℝ) + 1) * Real.log k := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 1 + ((a : ℝ) + 1) * ((k : ℝ) - 1) := by
        gcongr
        · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          norm_num at hh
          exact hh
        · exact Real.log_le_sub_one_of_pos hkp
      _ ≤ _ := by nlinarith [mul_nonneg (show (0 : ℝ) ≤ k - 8 * (a + 2) by linarith) hkp.le]
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hden : 0 < Real.log ((k : ℝ) ^ (a + 1)) := by
    apply Real.log_pos
    exact_mod_cast (one_lt_pow₀ (by omega : 1 < k) (by omega : a + 1 ≠ 0))
  have hlo : (2 * k ^ a : ℕ) ≤ ((k : ℝ) ^ (a + 1) * Real.log 2 - Real.log ((k : ℝ) ^ (a + 1) + 1)) /
      Real.log ((k : ℝ) ^ (a + 1)) := by
    apply (le_div_iff₀ hden).mpr
    push_cast
    rw [Real.log_pow]
    push_cast
    have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ) ^ a)
    have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ (a + 1))
    rw [pow_succ] at hh hlog ⊢
    nlinarith
  have hp := Chebyshev.pi_ge (k ^ (a + 1))
  push_cast at hp
  exact_mod_cast hlo.trans hp

noncomputable def band (k a : ℕ) := (k ^ (a + 1)).primesLE \ (k ^ a).primesLE

lemma eventually_band_card (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ k : ℕ in atTop, k ^ a ≤ (band k a).card := by
  filter_upwards [eventually_pi_power a ha, eventually_ge_atTop 1] with k hk hk1
  have hsub : (k ^ a).primesLE ⊆ (k ^ (a + 1)).primesLE := by
    intro p hp
    obtain ⟨hpk, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpk.trans (pow_le_pow_right₀ hk1 (by omega)), hpp⟩
  rw [band, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]
  have hh := primeCounting_le (k ^ a)
  omega

lemma mem_band {k a p : ℕ} (hp : p ∈ band k a) : Nat.Prime p ∧ k ^ a < p ∧ p ≤ k ^ (a + 1) := by
  obtain ⟨hp, hlo⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hup, hprime⟩ := Nat.mem_primesLE.mp hp
  refine ⟨hprime, ?_, hup⟩
  by_contra hn
  exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)

end PrimeSupply

end TreeEdit

end OAI
