import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.DyadicError

private theorem pow_le_one_aux (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    q^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih hq0).trans (by simpa using hq1)

private theorem pow_antitone_aux (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (a b : ℕ) (hab : a ≤ b) : q^b ≤ q^a := by
  have hb : a + (b-a) = b :=
    (Nat.add_comm a (b-a)).trans (Nat.sub_add_cancel hab)
  calc
    q^b = q^(a+(b-a)) := congrArg (fun n : ℕ => q^n) hb.symm
    _ = q^a * q^(b-a) := by rw [pow_add]
    _ ≤ q^a * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one_aux q hq0 hq1 (b-a)) (pow_nonneg hq0 a)
    _ = q^a := mul_one _

theorem half_power_le_quarter (d n : ℕ) (hd : 1 ≤ d) :
    (1/2 : ℝ)^(3*d*n) ≤ (1/4 : ℝ)^n := by
  have h3 : 2 ≤ 3*d := le_trans (by decide : 2 ≤ 3)
    (by simpa using Nat.mul_le_mul_left 3 hd)
  have hexp : 2*n ≤ 3*d*n := Nat.mul_le_mul_right n h3
  calc
    (1/2 : ℝ)^(3*d*n) ≤ (1/2 : ℝ)^(2*n) :=
      pow_antitone_aux (1/2) (by norm_num) (by norm_num) _ _ hexp
    _ = (1/4 : ℝ)^n := by
      rw [pow_mul]
      congr 1
      norm_num

def quarterSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1/4 : ℝ)^i

theorem quarterSum_nonneg (n : ℕ) : 0 ≤ quarterSum n := by
  unfold quarterSum
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (by norm_num : (0:ℝ)≤1/4) i)

theorem quarterSum_residual (n : ℕ) :
    quarterSum n + (4/3 : ℝ)*(1/4 : ℝ)^n = 4/3 := by
  induction n with
  | zero => norm_num [quarterSum]
  | succ n ih =>
    have hstep : quarterSum (n+1) = quarterSum n + (1/4 : ℝ)^n := by
      exact Finset.sum_range_succ _ _
    rw [hstep, pow_succ]
    nlinarith

theorem quarterSum_le (n : ℕ) : quarterSum n ≤ (4/3 : ℝ) := by
  have hp : (0 : ℝ) ≤ (1/4 : ℝ)^n := pow_nonneg (by norm_num) n
  have h := quarterSum_residual n
  nlinarith

def quarterError (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if i=0 ∧ j=0 then 0 else (1/4 : ℝ)^(i+j)

theorem quarterError_add_one (n : ℕ) (hn : 0 < n) :
    quarterError n + 1 = (quarterSum n)^2 := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hpair (i j : ℕ) :
      (if i=0 ∧ j=0 then (0:ℝ) else (1/4 : ℝ)^(i+j)) +
        (if i=0 ∧ j=0 then (1:ℝ) else 0) =
          (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [hi,hj,pow_add]
  have hsum : quarterError n +
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i=0 ∧ j=0 then (1:ℝ) else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    unfold quarterError
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hpair i j
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range n, if i=0 ∧ j=0 then (1:ℝ) else 0) =
        if i=0 then 1 else 0 := by
    by_cases hi : i=0
    · simp [hi,h0]
    · simp [hi]
  have hdelta : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i=0 ∧ j=0 then (1:ℝ) else 0) = 1 := by
    simp_rw [hinner]
    simp [h0]
  have hproduct : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (1/4 : ℝ)^i * (1/4 : ℝ)^j) = (quarterSum n)^2 := by
    simp only [quarterSum,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hdelta,hproduct] at hsum
  exact hsum

theorem quarterError_le_seven_ninths (n : ℕ) (hn : 0 < n) :
    quarterError n ≤ (7/9 : ℝ) := by
  have hbound := quarterSum_le n
  have hnonneg := quarterSum_nonneg n
  have hsq := mul_le_mul hbound hbound hnonneg (by norm_num : (0:ℝ)≤4/3)
  have hid := quarterError_add_one n hn
  nlinarith

def dyadicError (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
    if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))

theorem dyadicError_le_quarterError (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ quarterError (d+1) := by
  unfold dyadicError quarterError
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hzero : i=0 ∧ j=0
  · simp [hzero]
  · simp only [hzero]
    exact half_power_le_quarter d (i+j) hd

theorem dyadicError_le_seven_ninths (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ (7/9 : ℝ) :=
  (dyadicError_le_quarterError d hd).trans
    (quarterError_le_seven_ninths (d+1) (Nat.succ_pos d))

theorem finite_dyadic_error_le_one (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
      if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))) ≤ 1 := by
  change dyadicError d ≤ 1
  exact (dyadicError_le_seven_ninths d hd).trans (by norm_num)

end UniqueGamesTheorem.Appendix.DyadicError

end

end

end OAI
