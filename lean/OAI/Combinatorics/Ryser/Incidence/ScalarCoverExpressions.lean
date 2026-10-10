import OAI.Combinatorics.Ryser.Incidence.ScalarCover
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

inductive ScalarExpression (E : Finset F) : F → ℕ → Prop
  | seed {c : F} (hc : c ∈ E ∨ c = 0 ∨ c = 1) :
      ScalarExpression E c 0
  | neg {c : F} {m : ℕ} (h : ScalarExpression E c m) :
      ScalarExpression E (-c) (m + 1)
  | add {c d : F} {m n : ℕ}
      (hc : ScalarExpression E c m) (hd : ScalarExpression E d n) :
      ScalarExpression E (c + d) (m + n + 1)
  | sub {c d : F} {m n : ℕ}
      (hc : ScalarExpression E c m) (hd : ScalarExpression E d n) :
      ScalarExpression E (c - d) (m + n + 1)
  | mul {c d : F} {m n : ℕ}
      (hc : ScalarExpression E c m) (hd : ScalarExpression E d n) :
      ScalarExpression E (c * d) (m + n + 1)
  | inv {c : F} {m : ℕ}
      (h : ScalarExpression E c m) (hc : c ≠ 0) :
      ScalarExpression E c⁻¹ (m + 1)

def scalarCoverExponent : ℕ → ℕ
  | 0 => 4
  | m + 1 => 3 * scalarCoverExponent m + 5

@[simp] theorem scalarCoverExponent_zero :
    scalarCoverExponent 0 = 4 := rfl

@[simp] theorem scalarCoverExponent_succ (m : ℕ) :
    scalarCoverExponent (m + 1) =
      3 * scalarCoverExponent m + 5 := rfl

theorem scalarCoverExponent_le_succ (m : ℕ) :
    scalarCoverExponent m ≤ scalarCoverExponent (m + 1) := by
  rw [scalarCoverExponent_succ]
  omega

theorem scalarCoverExponent_monotone :
    Monotone scalarCoverExponent :=
  monotone_nat_of_le_succ scalarCoverExponent_le_succ

theorem scalarCoverExponent_ge_four (m : ℕ) :
    4 ≤ scalarCoverExponent m :=
  scalarCoverExponent_monotone (Nat.zero_le m)

theorem scalarCoverExponent_twice_add (m : ℕ) :
    2 * scalarCoverExponent m + 5 = 13 * 3 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [scalarCoverExponent_succ, pow_succ]
      omega

theorem scalarCoverExponent_closed_form (m : ℕ) :
    scalarCoverExponent m = (13 * 3 ^ m - 5) / 2 := by
  have h := scalarCoverExponent_twice_add m
  omega

private theorem scalarCoverExponent_inv_bound (m : ℕ) :
    scalarCoverExponent m + 3 ≤ scalarCoverExponent (m + 1) := by
  rw [scalarCoverExponent_succ]
  omega

private theorem scalarCoverExponent_add_bound (m n : ℕ) :
    scalarCoverExponent m + scalarCoverExponent n + 5 ≤
      scalarCoverExponent (m + n + 1) := by
  have hm := scalarCoverExponent_monotone
    (show m ≤ m + n by omega)
  have hn := scalarCoverExponent_monotone
    (show n ≤ m + n by omega)
  rw [scalarCoverExponent_succ]
  omega

private theorem scalarCoverExponent_mul_bound (m n : ℕ) :
    scalarCoverExponent n + 2 * scalarCoverExponent m + 5 ≤
      scalarCoverExponent (m + n + 1) := by
  have hm := scalarCoverExponent_monotone
    (show m ≤ m + n by omega)
  have hn := scalarCoverExponent_monotone
    (show n ≤ m + n by omega)
  rw [scalarCoverExponent_succ]
  omega

variable {B E : Finset F} {K : ℝ}

theorem ScalarExpression.scalarCovered
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hEB : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    {c : F} {n : ℕ} (h : ScalarExpression E c n) :
    ScalarCovered B K c (scalarCoverExponent n) := by
  have hK1 : 1 ≤ K := one_le_two.trans hK
  induction h with
  | seed hc =>
      exact scalarCovered_seed hB hK hD hEB hc
  | neg h ih =>
      exact scalarCovered_mono hK1 (scalarCovered_neg ih)
        (scalarCoverExponent_le_succ _)
  | add hc hd ihc ihd =>
      exact scalarCovered_mono hK1
        (scalarCovered_add hB hK hD ihc ihd)
        (scalarCoverExponent_add_bound _ _)
  | sub hc hd ihc ihd =>
      exact scalarCovered_mono hK1
        (scalarCovered_sub hB hK hD ihc ihd)
        (scalarCoverExponent_add_bound _ _)
  | mul hc hd ihc ihd =>
      exact scalarCovered_mono hK1
        (scalarCovered_mul hB hK hD ihc ihd)
        (scalarCoverExponent_mul_bound _ _)
  | inv h hc ih =>
      exact scalarCovered_mono hK1
        (scalarCovered_inv hB hK hD ih hc)
        (scalarCoverExponent_inv_bound _)

theorem ScalarExpression.scalarCovered_of_le
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hEB : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    {c : F} {n m : ℕ}
    (h : ScalarExpression E c n) (hnm : n ≤ m) :
    ScalarCovered B K c (scalarCoverExponent m) :=
  scalarCovered_mono (one_le_two.trans hK)
    (ScalarExpression.scalarCovered hB hK hD hEB h)
    (scalarCoverExponent_monotone hnm)

theorem ScalarExpression.card_add_of_le
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hEB : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    {c : F} {n m : ℕ}
    (h : ScalarExpression E c n) (hnm : n ≤ m) :
    ((B + c • B).card : ℝ) ≤
      K ^ (scalarCoverExponent m + 3) * (B.card : ℝ) :=
  scalarCovered_card_add hB hK hD
    (ScalarExpression.scalarCovered_of_le hB hK hD hEB h hnm)

theorem ScalarExpression.card_add_subset_of_le
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hCost : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    (hEB : E ⊆ B)
    {c : F} {n m : ℕ}
    (h : ScalarExpression E c n) (hnm : n ≤ m) :
    ((E + c • E).card : ℝ) ≤
      K ^ (scalarCoverExponent m + 3) * (B.card : ℝ) := by
  have hsub : E + c • E ⊆ B + c • B :=
    Finset.add_subset_add hEB
      (Finset.smul_finset_subset_smul_finset hEB)
  have hcard :
      ((E + c • E).card : ℝ) ≤ ((B + c • B).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  exact hcard.trans
    (ScalarExpression.card_add_of_le hB hK hD hCost h hnm)

theorem scalarExpression_ratio
    {x x' y y' : F}
    (hx : x ∈ E) (hx' : x' ∈ E)
    (hy : y ∈ E) (hy' : y' ∈ E)
    (hyy' : y ≠ y') :
    ScalarExpression E ((x - x') / (y - y')) 4 := let _ := instDecidableEqF; by
  have hnum : ScalarExpression E (x - x') 1 :=
    ScalarExpression.sub
      (ScalarExpression.seed (Or.inl hx))
      (ScalarExpression.seed (Or.inl hx'))
  have hden : ScalarExpression E (y - y') 1 :=
    ScalarExpression.sub
      (ScalarExpression.seed (Or.inl hy))
      (ScalarExpression.seed (Or.inl hy'))
  have hinv : ScalarExpression E (y - y')⁻¹ 2 :=
    ScalarExpression.inv hden (sub_ne_zero.mpr hyy')
  simpa only [div_eq_mul_inv] using
    (ScalarExpression.mul hnum hinv)

end RyserCoveringCounterexample.Incidence

end OAI
