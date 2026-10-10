import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

namespace OAI

/-! A fixed number of residue classes separates the dyadic annuli in
the ordinary synthesis estimate. The number depends only on the two
fixed annular constants, independently of the number of scales. -/

noncomputable section
namespace LipschitzHilbert

theorem exists_dyadic_annular_separation {lower upper : ℝ} (hlower : 0 < lower) :
    ∃ q : ℕ, 0 < q ∧ ∀ j k : ℕ, j < k → j % q = k % q →
      upper*(2:ℝ)^j < lower*(2:ℝ)^k := by
  obtain ⟨q,hq⟩ := pow_unbounded_of_one_lt (upper/lower) (by norm_num : (1:ℝ) < 2)
  let Q := max 1 q
  have hQ : 0 < Q := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
  have hbase : upper < lower*(2:ℝ)^Q := by
    have hpow : (2:ℝ)^q ≤ 2^Q :=
      pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    simpa only [mul_comm] using (div_lt_iff₀ hlower).mp (hq.trans_le hpow)
  refine ⟨Q,hQ,?_⟩
  intro j k hjk hmod
  have hdiv : Q ∣ k-j := Nat.ModEq.dvd' hmod
  have hle : Q ≤ k-j := Nat.le_of_dvd (Nat.sub_pos_of_lt hjk) hdiv
  have hindex : Q+j ≤ k := by omega
  calc
    upper*(2:ℝ)^j < (lower*2^Q)*2^j :=
      mul_lt_mul_of_pos_right hbase (by positivity)
    _ = lower*(2:ℝ)^(Q+j) := by rw [pow_add]; ring
    _ ≤ lower*(2:ℝ)^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hindex) hlower.le

end LipschitzHilbert

end

end OAI
