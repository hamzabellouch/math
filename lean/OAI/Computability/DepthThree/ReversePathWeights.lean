import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace OAI

universe uDepth1

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [Fintype V]

def bernoulliWeight (p : ℝ) (R : Finset V) : ℝ :=
  p ^ R.card * (1 - p) ^ (Fintype.card V - R.card)

theorem bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Finset V) : 0 ≤ bernoulliWeight p R := by
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem bernoulliWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (R : Finset V) : 0 < bernoulliWeight p R := by
  exact mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)

theorem sum_bernoulliWeight (p : ℝ) :
    ∑ R : Finset V, bernoulliWeight p R = 1 := by
  classical
  have hp : p + (1 - p) = 1 := by ring
  simpa only [bernoulliWeight, hp, Finset.prod_const, Finset.card_compl, one_pow]
    using (Fintype.prod_add (fun _ : V => p) (fun _ : V => 1 - p)).symm

variable [DecidableEq V]

theorem bernoulliWeight_disjoint_balance (p : ℝ) (R D : Finset V)
    (hRD : Disjoint R D) :
    bernoulliWeight p (R ∪ D) * (1 - p) ^ D.card =
      bernoulliWeight p R * p ^ D.card := by
  have hcard : R.card + D.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hRD]
    exact (R ∪ D).card_le_univ
  have hD : D.card ≤ Fintype.card V - R.card :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hcard)
  have hsplit : Fintype.card V - R.card =
      (Fintype.card V - (R.card + D.card)) + D.card := by
    rw [← Nat.sub_sub, Nat.sub_add_cancel hD]
  unfold bernoulliWeight
  rw [Finset.card_union_of_disjoint hRD, hsplit, pow_add, pow_add]
  ring

theorem bernoulliWeight_disjoint_union {p : ℝ} (_hp0 : 0 < p) (hp1 : p < 1)
    (R D : Finset V) (hRD : Disjoint R D) :
    bernoulliWeight p (R ∪ D) * (2 : ℝ) ^ D.card =
      bernoulliWeight p R * (2 * p / (1 - p)) ^ D.card := by
  have hq : (1 - p) ^ D.card ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (sub_pos.mpr hp1))
  rw [div_pow, mul_pow, ← mul_div_assoc]
  apply (eq_div_iff hq).2
  calc
    (bernoulliWeight p (R ∪ D) * (2 : ℝ) ^ D.card) * (1 - p) ^ D.card =
        (bernoulliWeight p (R ∪ D) * (1 - p) ^ D.card) * (2 : ℝ) ^ D.card := by
          ring
    _ = (bernoulliWeight p R * p ^ D.card) * (2 : ℝ) ^ D.card := by
          rw [bernoulliWeight_disjoint_balance p R D hRD]
    _ = bernoulliWeight p R * ((2 : ℝ) ^ D.card * p ^ D.card) := by ring

end DepthThreeLowerBound

end OAI
