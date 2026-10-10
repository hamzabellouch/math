import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionBlocks

namespace OAI

/-! # Frequency aggregation preserves each complete divisor comparison -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_correction_frequency_reindex (K Q : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b) =
      ∑ i ∈ Finset.range (Nat.log 2 K + 1), ∑ d ∈ Finset.Icc 1 Q,
        ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
          if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 Q, ∑ i ∈ Finset.range (Nat.log 2 K + 1),
        ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
          if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0 :=
      Finset.sum_congr rfl (fun d _ => quadratic_correction_frequency_sum K (F d))
    _ = _ := Finset.sum_comm

theorem quadratic_correction_frequency_bound (K Q : ℕ) (F : ℕ → ℕ → ℂ) (c : ℂ)
    (T : ℝ) (hband : ∀ i < Nat.log 2 K + 1,
      ‖c * (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
        if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0)‖ ≤ T) :
    ‖c * (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b)‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * T := by
  rw [quadratic_correction_frequency_reindex, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range (Nat.log 2 K + 1), T :=
      Finset.sum_le_sum (fun i hi => hband i (Finset.mem_range.mp hi))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem quadratic_frequency_block_le {K i : ℕ} (hK : 0 < K) (hi : i < Nat.log 2 K + 1) :
    2 ^ i ≤ K :=
  (Nat.pow_le_pow_right (by norm_num) (by omega : i ≤ Nat.log 2 K)).trans
    (Nat.pow_log_le_self 2 hK.ne')

end Ostmann

end OAI
