import OAI.NumberTheory.Ostmann.Construction.OriginalProductScale

namespace OAI

/-! # Transferring the chosen tails and dyadic block to the original theorem's bounds -/

namespace Ostmann

open scoped BigOperators Classical

theorem local_tail_size_transfer (a L V : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (hLU : L ≤ 2 * V ^ 2) :
    (a / 8) * Real.exp (L / 2) / V ^ 6 ≤ a * Real.exp (L / 2) / L ^ 3 := by
  have hp : L ^ 3 ≤ 8 * V ^ 6 := by
    have hh := pow_le_pow_left₀ hL.le hLU 3
    nlinarith only [hh]
  calc
    (a / 8) * Real.exp (L / 2) / V ^ 6 = a * Real.exp (L / 2) / (8 * V ^ 6) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hp

theorem dyadic_block_card_le (P : Finset ℕ) (z : ℕ)
    (hP : ∀ p ∈ P, z ≤ p ∧ p < 2 * z) : P.card ≤ z := by
  have hsub : P ⊆ Finset.Ico z (2 * z) := fun p hp => Finset.mem_Ico.mpr (hP p hp)
  have hh := Finset.card_le_card hsub
  simp only [Nat.card_Ico] at hh
  omega

theorem doubled_prime_endpoint_le_exp (z : ℕ) (hz : 0 < z) :
    ((2 * z : ℕ) : ℝ) ≤ Real.exp (Real.log z + 1) := by
  rw [Real.exp_add, Real.exp_log (by exact_mod_cast hz)]
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (Nat.cast_nonneg (α := ℝ) z)]

theorem original_upper_endpoint_power (z : ℕ) (L V : ℝ)
    (hz : 0 < z) (hV : 0 < V) (hLV : Real.log (z : ℝ) = V) (hL : 0 ≤ L)
    (hklog : (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V) (h13 : 13 * V ≤ L) :
    (((2 * z : ℕ) : ℝ) ^ originalMomentOrder L V) ≤ Real.exp (2 * L) := by
  have hzpos : 0 < 2 * (z : ℝ) := by positivity
  have he : Real.log (2 * (z : ℝ)) = V + Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by exact_mod_cast (Nat.ne_of_gt hz)), hLV, add_comm]
  push_cast
  rw [← Real.exp_log hzpos, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [he]
  have hu := (originalMomentOrder_scale L V hL hV).2.2
  nlinarith only [hu, hklog, h13]

theorem original_tail_weight_cutoff (L V B Q : ℝ) (hV : 0 < V)
    (h13 : 13 * V ≤ L) (hQ : 0 < Q) (hQU : Q ≤ Real.exp (V / 50))
    (hB : B ^ 2 ≤ Real.exp (12 * V / 25)) : B ^ 2 < Real.exp L / Q := by
  apply (lt_div_iff₀ hQ).mpr
  have hh := mul_le_mul hB hQU hQ.le (Real.exp_nonneg _)
  have he : Real.exp (12 * V / 25) * Real.exp (V / 50) = Real.exp (V / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hh
  exact hh.trans_lt (Real.exp_lt_exp.mpr (by linarith))

end Ostmann

end OAI
