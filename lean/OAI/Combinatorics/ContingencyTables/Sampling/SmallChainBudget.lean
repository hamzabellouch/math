import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphPoincareBudget

namespace OAI

/-! # Actual first-paper small-chain constants -/

namespace ContingencyTables

lemma small_chain_poincare_constant (d : ℕ) (hd : 14 ≤ d) :
    128*(d:ℝ)^2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6) ≤ (d:ℝ)^160 := by
  have hcoef : (98560:ℝ) ≤ (d:ℝ)^34 := by
    exact_mod_cast (show 98560 ≤ d^34 from
      (by norm_num : 98560 ≤ 14^34).trans (Nat.pow_le_pow_left hd 34))
  calc
    _ = 98560*(d:ℝ)^126 := by push_cast; ring
    _ ≤ (d:ℝ)^34*(d:ℝ)^126 := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

lemma completion_rejection_lt_half (d : ℕ) (hd : 14 ≤ d) :
    40*(d:ℝ)^5/((d^12:ℕ):ℝ) < 1/2 := by
  have hpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : (80:ℝ) < (d:ℝ)^7 := by
    exact_mod_cast (show 80 < d^7 from
      lt_of_lt_of_le (by norm_num : 80 < 14^7) (Nat.pow_le_pow_left hd 7))
  have hmul : 80*(d:ℝ)^5 < (d:ℝ)^12 := by
    calc
      _ < (d:ℝ)^7*(d:ℝ)^5 := mul_lt_mul_of_pos_right hp (pow_pos hpos 5)
      _ = _ := by ring
  push_cast
  apply (div_lt_iff₀ (pow_pos hpos 12)).mpr
  linarith

end ContingencyTables

end OAI
