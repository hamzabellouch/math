import Mathlib.Tactic

namespace OAI

namespace Balanced.Local
noncomputable section

theorem small_reuse_cost_le (q B x C : ℝ) (d κ : ℕ)
    (hq : 0 < q) (hB : 1 ≤ B) (hx : 0 ≤ x) (hC : 0 ≤ C) (hk : κ ≤ 3) :
    (C * x ^ d * (2 * B / q) ^ (3 - κ)) / q ^ κ ≤
      8 * C * x ^ d * (B ^ 3 / q ^ 3) := by
  have hpow : (2 * B) ^ (3 - κ) ≤ 8 * B ^ 3 := by
    calc
      (2 * B) ^ (3 - κ) ≤ (2 * B) ^ 3 :=
        pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
      _ = 8 * B ^ 3 := by ring
  calc
    (C * x ^ d * (2 * B / q) ^ (3 - κ)) / q ^ κ =
        C * x ^ d * (2 * B) ^ (3 - κ) / q ^ 3 := by
      rw [div_pow, mul_div_assoc, div_div, ← pow_add, Nat.sub_add_cancel hk]
      ring
    _ ≤ C * x ^ d * (8 * B ^ 3) / q ^ 3 := by gcongr
    _ = _ := by ring

theorem small_reuse_envelope_le (q B C A : ℝ) (b d a κ : ℕ)
    (hq : 0 < q) (hB : 1 ≤ B) (hb : 1 ≤ b) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hk : κ ≤ 3) (ha : d + 4 ≤ a) :
    (4 * (b : ℝ)) ^ 4 * A ^ b / (b.factorial : ℝ) *
      ((C * (b : ℝ) ^ d * (2 * B / q) ^ (3 - κ)) / q ^ κ) ≤
      (2048 * C) * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) * (B ^ 3 / q ^ 3)) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hcost := small_reuse_cost_le q B (b : ℝ) C d κ hq hB (Nat.cast_nonneg _) hC hk
  calc
    _ ≤ (4 * (b : ℝ)) ^ 4 * A ^ b / (b.factorial : ℝ) *
        (8 * C * (b : ℝ) ^ d * (B ^ 3 / q ^ 3)) := by gcongr
    _ = (2048 * C) * (((b : ℝ) ^ (d + 4) * A ^ b / (b.factorial : ℝ)) *
        (B ^ 3 / q ^ 3)) := by rw [pow_add]; ring
    _ ≤ _ := by
      have hp := pow_le_pow_right₀ hbR ha
      gcongr

theorem two_reuse_envelope_le (q B D A : ℝ) (b a : ℕ)
    (hq : 0 < q) (hB : 1 ≤ B) (hb : 1 ≤ b) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (ha : 7 ≤ a) :
    (4 * (b : ℝ)) ^ 4 * A ^ b / (b.factorial : ℝ) *
      ((D * (b : ℝ) ^ 3 / q) / q ^ 2) ≤
      (256 * D) * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) * (B ^ 3 / q ^ 3)) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hB3 : (1 : ℝ) ≤ B ^ 3 := one_le_pow₀ hB
  calc
    _ = (256 * D) * (((b : ℝ) ^ 7 * A ^ b / (b.factorial : ℝ)) *
        (1 / q ^ 3)) := by ring
    _ ≤ _ := by
      have hp := pow_le_pow_right₀ hbR ha
      gcongr

end
end Balanced.Local

end OAI
