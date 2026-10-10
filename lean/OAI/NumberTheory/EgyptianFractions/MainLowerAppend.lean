import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337
namespace MainLower

/-- Appending the remainder denominator and sorting reduces the lower-bound
argument to a coordinate bound for possibly repeated unit fractions. -/
theorem denominator_le_of_sum
    (hbound : ∀ s : ℕ, ∀ d : Fin s → ℕ,
      (∀ i, 1 ≤ d i) → Monotone d →
      (∑ i : Fin s, (1 : ℚ) / (d i : ℚ)) = 1 →
      ∀ i : Fin s, d i ≤ s ^ (2 ^ i.val))
    {b k : ℕ} (hb : 2 ≤ b) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) =
      ((b - 1 : ℕ) : ℚ) / (b : ℚ)) :
    b ≤ (k + 1) ^ (2 ^ k) := by
  let d : Fin (k + 1) → ℕ := Fin.snoc n b
  let e := Tuple.sort d
  have hd : ∀ i, 1 ≤ d i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [d] using (show 1 ≤ b by omega)
    · simpa [d] using hn j
  have hdsum : (∑ i : Fin (k + 1), (1 : ℚ) / (d i : ℚ)) = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [d, Fin.snoc_castSucc, Fin.snoc_last]
    rw [hsum]
    have hb0 : (b : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_sub (show 1 ≤ b by omega)]
    push_cast
    field_simp
    ring
  have hsorted : (∑ i : Fin (k + 1), (1 : ℚ) / ((d ∘ e) i : ℚ)) = 1 := by
    calc
      _ = ∑ i : Fin (k + 1), (1 : ℚ) / (d i : ℚ) :=
        Equiv.sum_comp e (fun i => (1 : ℚ) / (d i : ℚ))
      _ = 1 := hdsum
  have hcoord := hbound (k + 1) (d ∘ e) (fun i => hd (e i))
    (Tuple.monotone_sort d) hsorted (e.symm (Fin.last k))
  have hpow : (k + 1) ^ (2 ^ (e.symm (Fin.last k)).val) ≤
      (k + 1) ^ (2 ^ k) := by
    apply Nat.pow_le_pow_right (by omega)
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.le_of_lt_succ (e.symm (Fin.last k)).isLt
  have hbcoord : b ≤ (k + 1) ^ (2 ^ (e.symm (Fin.last k)).val) := by
    simpa [Function.comp_def, d] using hcoord
  exact hbcoord.trans hpow

/-- A convenient absolute constant for the elementary lower bound. -/
theorem log_log_le_twice {b k : ℕ} (hb : 2 ≤ b)
    (hbk : b ≤ (k + 1) ^ (2 ^ k)) :
    Real.log (Real.log (b : ℝ)) ≤ 2 * (k : ℝ) := by
  have hk : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst k
    norm_num at hbk
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlog : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hk1
  have hbpos : (0 : ℝ) < b := by positivity
  have hp : (b : ℝ) ≤ ((k : ℝ) + 1) ^ (2 ^ k) := by exact_mod_cast hbk
  have hfirst := Real.log_le_log hbpos hp
  rw [Real.log_pow] at hfirst
  have hbLog : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hsecond := Real.log_le_log hbLog hfirst
  rw [Real.log_mul (by positivity) (ne_of_gt hlog)] at hsecond
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_cast
  rw [hcast, Real.log_pow] at hsecond
  have htwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  have hsmall : Real.log ((k : ℝ) + 1) ≤ (k : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
  have hsmall' : Real.log (Real.log ((k : ℝ) + 1)) ≤ (k : ℝ) := by
    calc
      Real.log (Real.log ((k : ℝ) + 1)) ≤ Real.log ((k : ℝ) + 1) :=
        Real.log_le_log hlog (by linarith)
      _ ≤ (k : ℝ) := hsmall
  nlinarith

end MainLower
end Problem337

end

end OAI
