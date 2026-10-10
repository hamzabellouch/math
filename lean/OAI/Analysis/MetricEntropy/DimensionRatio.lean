import OAI.Analysis.MetricEntropy.FormDimension
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Exact dimension ratio and rank lower bound

These are identities for the canonical symmetric-form coefficient count.
The ratio is used in the entropy estimate; the lower bound ensures that
the constructed ambient dimensions diverge as the rank increases.
-/

namespace MetricEntropyDuality

/-- The multiplicative recurrence avoids any natural-number division. -/
theorem formDimension_mul_degree {r h : ℕ} (hr : 0 < r) (hh : 0 < h) :
    formDimension r h * h = formDimension r (h - 1) * (r + h - 1) := by
  cases h with
  | zero => omega
  | succ k =>
      have hk : r + k - 1 + 1 = r + k := by omega
      have hrec := Nat.add_one_mul_choose_eq (r + k - 1) k
      rw [hk] at hrec
      simpa only [formDimension, Nat.add_succ, Nat.succ_sub_one, Nat.mul_comm] using
        hrec.symm

/-- The exact ratio of the previous-degree and current-degree dimensions. -/
theorem formDimension_prev_div {r h : ℕ} (hr : 0 < r) (hh : 0 < h) :
    (formDimension r (h - 1) : ℝ) / (formDimension r h : ℝ) =
      (h : ℝ) / ((r : ℝ) + h - 1) := by
  have hD : 0 < (formDimension r h : ℝ) :=
    Nat.cast_pos.mpr (formDimension_pos hr)
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast Nat.succ_le_of_lt hh
  have hden : 0 < (r : ℝ) + h - 1 := by linarith
  have hcast : ((r + h - 1 : ℕ) : ℝ) = (r : ℝ) + h - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r + h), Nat.cast_add, Nat.cast_one]
  have hrec : ((formDimension r h * h : ℕ) : ℝ) =
      ((formDimension r (h - 1) * (r + h - 1) : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) (formDimension_mul_degree hr hh)
  rw [Nat.cast_mul, Nat.cast_mul, hcast] at hrec
  apply (div_eq_div_iff hD.ne' hden.ne').mpr
  exact hrec.symm.trans (mul_comm _ _)

/-- Every positive degree has at least as many coefficients as the rank. -/
theorem rank_le_formDimension {r h : ℕ} (hr : 0 < r) (hh : 0 < h) :
    r ≤ formDimension r h := by
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hchoose : r.choose (r - 1) = r := by
    simpa only [hpred] using Nat.choose_succ_self_right (r - 1)
  have htop : r ≤ r + h - 1 := by omega
  have hdegree : h ≤ r + h - 1 := by omega
  have hsub : r + h - 1 - h = r - 1 := by omega
  calc
    r = r.choose (r - 1) := hchoose.symm
    _ ≤ (r + h - 1).choose (r - 1) := Nat.choose_le_choose _ htop
    _ = formDimension r h := by
      unfold formDimension
      rw [← hsub]
      exact Nat.choose_symm hdegree

/-- A field with at least two elements has more coefficient vectors than
the number of coefficient coordinates. -/
theorem formDimension_le_prime_power {r h p : ℕ} (hp : 2 ≤ p) :
    formDimension r h ≤ p ^ formDimension r h :=
  (show formDimension r h < 2 ^ formDimension r h from Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_left hp _)

/-- The explicit chain connecting rank to the actual ambient dimension. -/
theorem dimension_growth_chain {r h p n : ℕ} (hr : 0 < r) (hh : 0 < h)
    (hp : 2 ≤ p) (hn : p ^ formDimension r h ≤ n) :
    r ≤ formDimension r h ∧ formDimension r h ≤ p ^ formDimension r h ∧
      p ^ formDimension r h ≤ n :=
  ⟨rank_le_formDimension hr hh, formDimension_le_prime_power hp, hn⟩

theorem rank_le_ambientDimension {r h p n : ℕ} (hr : 0 < r) (hh : 0 < h)
    (hp : 2 ≤ p) (hn : p ^ formDimension r h ≤ n) : r ≤ n :=
  (rank_le_formDimension hr hh).trans ((formDimension_le_prime_power hp).trans hn)

theorem ambientDimension_pos {r h p n : ℕ} (hr : 0 < r) (hh : 0 < h)
    (hp : 2 ≤ p) (hn : p ^ formDimension r h ≤ n) : 0 < n :=
  hr.trans_le (rank_le_ambientDimension hr hh hp hn)

end MetricEntropyDuality

end OAI
