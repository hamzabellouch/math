import OAI.NumberTheory.Ostmann.Supply.TailSieveParameters

namespace OAI

/-! # Size and endpoint bounds at the rounded square-root cutoff -/
namespace Ostmann
open Filter

theorem sqrt_sieve_geometry (N : ℕ) (T : ℝ) (hT : 3 * ((N : ℝ) + 3) ≤ T) :
    let Q := ⌊Real.exp (T / 2)⌋₊
    1 ≤ Q ∧ Real.exp T / 4 ≤ (Q : ℝ) ^ 2 ∧
      (Real.exp T + 1) + (Q : ℝ) ^ 2 ≤ 3 * Real.exp T ∧
      N + Q ≤ summandTailCutoff T := by
  intro Q
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hT0 : 0 ≤ T := by linarith
  have hs : 2 ≤ Real.exp (T / 2) := by linarith [Real.add_one_le_exp (T / 2)]
  have hQ : 1 ≤ Q := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hQu : (Q : ℝ) ≤ Real.exp (T / 2) := Nat.floor_le (Real.exp_nonneg _)
  have hQl : Real.exp (T / 2) / 2 ≤ (Q : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (T / 2))
    change Real.exp (T / 2) - 1 < (Q : ℝ) at hh
    linarith
  have heq : Real.exp (T / 2) ^ 2 = Real.exp T := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hQpos : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hepos := Real.exp_nonneg (T / 2)
  have hsqU : (Q : ℝ) ^ 2 ≤ Real.exp T := by nlinarith only [hQu, hQpos, hepos, heq]
  have hsqL : Real.exp T / 4 ≤ (Q : ℝ) ^ 2 := by nlinarith only [hQl, hQpos, hepos, heq]
  refine ⟨hQ, hsqL, ?_, ?_⟩
  · linarith [Real.one_le_exp hT0]
  · have hN : (N : ℝ) + 3 ≤ Real.exp (2 * T / 5) := by
      linarith [Real.add_one_le_exp (2 * T / 5)]
    have hm := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (T / 2))
    have hid : Real.exp (T / 2) * Real.exp (2 * T / 5) = Real.exp (9 * T / 10) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hid] at hm
    have hh := mul_nonneg (sub_nonneg.mpr (hs.trans' (by norm_num : (1 : ℝ) ≤ 2)))
      (show 0 ≤ (N : ℝ) + 2 by positivity)
    have hf := Nat.sub_one_lt_floor (Real.exp (9 * T / 10))
    change Real.exp (9 * T / 10) - 1 < (summandTailCutoff T : ℝ) at hf
    have hfinal : (N : ℝ) + Q ≤ (summandTailCutoff T : ℝ) := by
      nlinarith only [hm, hh, hf, hQu]
    exact_mod_cast hfinal

theorem eventual_sqrt_sieve_geometry (N : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      let Q := ⌊Real.exp (Real.exp L / 2)⌋₊
      1 ≤ Q ∧ Real.exp (Real.exp L) / 4 ≤ (Q : ℝ) ^ 2 ∧
        (Real.exp (Real.exp L) + 1) + (Q : ℝ) ^ 2 ≤ 3 * Real.exp (Real.exp L) ∧
        N + Q ≤ summandTailCutoff (Real.exp L) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hL
  exact sqrt_sieve_geometry N (Real.exp L) hL

end Ostmann

end OAI
