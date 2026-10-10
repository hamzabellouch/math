import OAI.Combinatorics.DiscreteConvexity.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Dyadic bins for positive weights

The exponent of a weight is determined by the first power of `1 / 2`
strictly below it.  In particular, a weight equal to a dyadic endpoint
belongs to the bin whose upper endpoint it equals.
-/

namespace TalagrandDiscreteConvexity

/-- The dyadic exponent of a positive weight.  Its value at a nonpositive
weight is irrelevant to the bin partition and is fixed to zero. -/
noncomputable def binExponent (w : ℝ) : ℕ := by
  classical
  exact if hw : 0 < w then
    Nat.find (exists_pow_lt_of_lt_one hw (by norm_num : (1 / 2 : ℝ) < 1)) - 1
  else 0

/-- Every positive weight at most one lies in its specified dyadic bin. -/
theorem binExponent_spec {w : ℝ} (hwpos : 0 < w) (hwle : w ≤ 1) :
    (1 / 2 : ℝ) ^ (binExponent w + 1) < w ∧
      w ≤ (1 / 2 : ℝ) ^ binExponent w := by
  classical
  let ex : ∃ h : ℕ, (1 / 2 : ℝ) ^ h < w :=
    exists_pow_lt_of_lt_one hwpos (by norm_num : (1 / 2 : ℝ) < 1)
  have hcross : (1 / 2 : ℝ) ^ Nat.find ex < w := Nat.find_spec ex
  have hne : Nat.find ex ≠ 0 := by
    intro hz
    have : (1 : ℝ) < w := by simpa only [hz, pow_zero] using hcross
    exact (not_lt_of_ge hwle) this
  have hexp : binExponent w = Nat.find ex - 1 := by
    simp only [binExponent, dite_eq_left hwpos]
  rw [hexp]
  constructor
  · simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)] using hcross
  · exact le_of_not_gt (Nat.find_min ex (Nat.sub_one_lt hne))

theorem binExponent_lower {w : ℝ} (hwpos : 0 < w) (hwle : w ≤ 1) :
    (1 / 2 : ℝ) ^ (binExponent w + 1) < w :=
  (binExponent_spec hwpos hwle).1

theorem binExponent_upper {w : ℝ} (hwpos : 0 < w) (hwle : w ≤ 1) :
    w ≤ (1 / 2 : ℝ) ^ binExponent w :=
  (binExponent_spec hwpos hwle).2

/-- A dyadic upper bound on a weight gives a lower bound on its bin index. -/
theorem le_binExponent_of_le_pow {w : ℝ} {n : ℕ} (hwpos : 0 < w)
    (hwn : w ≤ (1 / 2 : ℝ) ^ n) : n ≤ binExponent w := by
  have hwle : w ≤ 1 :=
    hwn.trans (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hpow : (1 / 2 : ℝ) ^ (binExponent w + 1) < (1 / 2 : ℝ) ^ n :=
    (binExponent_lower hwpos hwle).trans_le hwn
  have hn : n < binExponent w + 1 :=
    (pow_lt_pow_iff_right_of_lt_one₀
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).mp hpow
  exact Nat.lt_succ_iff.mp hn

theorem le_binExponent_of_lt_pow {w : ℝ} {n : ℕ} (hwpos : 0 < w)
    (hwn : w < (1 / 2 : ℝ) ^ n) : n ≤ binExponent w :=
  le_binExponent_of_le_pow hwpos hwn.le

/-- The half-open bins are disjoint, including at their dyadic endpoints. -/
theorem binExponent_eq_of_bounds {w : ℝ} {h : ℕ}
    (hlo : (1 / 2 : ℝ) ^ (h + 1) < w)
    (hhi : w ≤ (1 / 2 : ℝ) ^ h) : binExponent w = h := by
  have hwpos : 0 < w := (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _).trans hlo
  have hwle : w ≤ 1 :=
    hhi.trans (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hpow : (1 / 2 : ℝ) ^ (h + 1) < (1 / 2 : ℝ) ^ binExponent w :=
    hlo.trans_le (binExponent_upper hwpos hwle)
  have hh : binExponent w < h + 1 :=
    (pow_lt_pow_iff_right_of_lt_one₀
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).mp hpow
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hh) (le_binExponent_of_le_pow hwpos hhi)

/-- The form used when assigning all residual weights to bins of index at
least their support size. -/
theorem exists_dyadic_bin {w : ℝ} {n : ℕ} (hwpos : 0 < w)
    (hwn : w < (1 / 2 : ℝ) ^ n) :
    ∃ h : ℕ, n ≤ h ∧ (1 / 2 : ℝ) ^ (h + 1) < w ∧ w ≤ (1 / 2 : ℝ) ^ h := by
  have hwle : w ≤ 1 :=
    hwn.le.trans (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  exact ⟨binExponent w, le_binExponent_of_lt_pow hwpos hwn,
    binExponent_spec hwpos hwle⟩

end TalagrandDiscreteConvexity

end OAI
