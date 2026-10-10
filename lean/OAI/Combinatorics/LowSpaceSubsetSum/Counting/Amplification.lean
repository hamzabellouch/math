import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

/-!
# The fixed repetition schedule

The numerical amplification estimate from the final section of
*A Low-Space Algorithm for Worst-Case Subset Sum*. The per-round failure bound
must be proved for the actual trials before this estimate applies.
-/

namespace LowSpaceSubsetSum

/-- The failure estimate for `u^120` fresh rounds with success at least `u^-110`.
The bound applies to any nonnegative per-round failure probability `q` below
the stated threshold. -/
theorem amplification_bound {u : ℕ} (hu : 2 ≤ u) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 - 1 / (u : ℝ) ^ 110) :
    q ^ (u ^ 120) < (1 / 3 : ℝ) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hu1 : (1 : ℝ) < u := by exact_mod_cast hu
  have hp : (u : ℝ) ^ 120 = (u : ℝ) ^ 110 * (u : ℝ) ^ 10 := by
    rw [← pow_add]
  have hratio : (u : ℝ) ^ 10 / (u ^ 120 : ℕ) = 1 / (u : ℝ) ^ 110 := by
    rw [Nat.cast_pow, hp]
    field_simp
  have ht : (u : ℝ) ^ 10 ≤ (u ^ 120 : ℕ) := by
    rw [Nat.cast_pow, hp]
    have hlarge : (1 : ℝ) ≤ (u : ℝ) ^ 110 := one_le_pow₀ hu1.le
    nlinarith [pow_pos hu0 10]
  have hexp := Real.one_sub_div_pow_le_exp_neg (n := u ^ 120) ht
  rw [hratio] at hexp
  have hqpow := pow_le_pow_left₀ hq0 hq (u ^ 120)
  have ht2 : (2 : ℝ) ≤ (u : ℝ) ^ 10 := by
    have hule : (u : ℝ) ≤ (u : ℝ) ^ 10 := le_self_pow₀ (by linarith) (by decide)
    have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
    exact hu2.trans hule
  have hstrict : 3 < Real.exp ((u : ℝ) ^ 10) := by
    have h := Real.add_one_lt_exp (by positivity : (u : ℝ) ^ 10 ≠ 0)
    linarith
  have hsmall : Real.exp (-((u : ℝ) ^ 10)) < (1 / 3 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 3)).mpr
    norm_num
    exact hstrict
  exact (hqpow.trans hexp).trans_lt hsmall

end LowSpaceSubsetSum

end OAI
