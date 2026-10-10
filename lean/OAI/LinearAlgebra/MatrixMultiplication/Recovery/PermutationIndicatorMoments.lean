import OAI.LinearAlgebra.MatrixMultiplication.Entropy.FiniteAverage
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators

variable {P : Type*} [DecidableEq P]

def membership (B : Finset P) (p : Equiv.Perm P) (i : P) : ℝ :=
  if p i ∈ B then 1 else 0

@[simp] theorem membership_sq (B : Finset P) (p : Equiv.Perm P) (i : P) :
    membership B p i * membership B p i = membership B p i := by
  simp only [membership]
  split_ifs <;> norm_num

theorem membership_nonneg (B : Finset P) (p : Equiv.Perm P) (i : P) :
    0 ≤ membership B p i := by
  simp only [membership]
  split_ifs <;> norm_num

theorem membership_le_one (B : Finset P) (p : Equiv.Perm P) (i : P) :
    membership B p i ≤ 1 := by
  simp only [membership]
  split_ifs <;> norm_num

variable [Fintype P]

theorem sum_membership (B : Finset P) (p : Equiv.Perm P) :
    (∑ i : P, membership B p i) = (B.card : ℝ) := by
  unfold membership
  rw [Equiv.sum_comp p (fun i => if i ∈ B then (1 : ℝ) else 0)]
  simp

theorem sum_perm_right (f : Equiv.Perm P → ℝ) (q : Equiv.Perm P) :
    (∑ p : Equiv.Perm P, f (p * q)) = ∑ p : Equiv.Perm P, f p := by
  exact Equiv.sum_comp (Equiv.mulRight q) f

theorem sum_membership_position_eq (B : Finset P) (i j : P) :
    (∑ p : Equiv.Perm P, membership B p i) =
      ∑ p : Equiv.Perm P, membership B p j := by
  calc
    _ = ∑ p : Equiv.Perm P, membership B (p * Equiv.swap i j) j := by
      simp [membership, Equiv.Perm.mul_apply]
    _ = _ := sum_perm_right (fun p => membership B p j) _

theorem card_mul_sum_membership (B : Finset P) (i : P) :
    (Fintype.card P : ℝ) * (∑ p : Equiv.Perm P, membership B p i) =
      (Fintype.card (Equiv.Perm P) : ℝ) * B.card := by
  calc
    _ = ∑ j : P, ∑ p : Equiv.Perm P, membership B p i := by simp
    _ = ∑ j : P, ∑ p : Equiv.Perm P, membership B p j := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_membership_position_eq B i j
    _ = ∑ p : Equiv.Perm P, ∑ j : P, membership B p j := Finset.sum_comm
    _ = _ := by simp [sum_membership]

theorem average_membership [Nonempty P] (B : Finset P) (i : P) :
    average (fun p : Equiv.Perm P => membership B p i) =
      (B.card : ℝ) / Fintype.card P := by
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm P) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  apply (div_eq_div_iff hp hn).2
  simpa only [mul_comm] using card_mul_sum_membership B i

theorem sum_membership_mul_position_eq (B : Finset P) {i j k : P}
    (hij : i ≠ j) (hik : i ≠ k) :
    (∑ p : Equiv.Perm P, membership B p i * membership B p j) =
      ∑ p : Equiv.Perm P, membership B p i * membership B p k := by
  calc
    _ = ∑ p : Equiv.Perm P,
        membership B (p * Equiv.swap j k) i *
          membership B (p * Equiv.swap j k) k := by
      simp [membership, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hij hik]
    _ = _ := sum_perm_right (fun p => membership B p i * membership B p k) _

theorem card_sub_one_mul_sum_membership_mul (B : Finset P) {i j : P}
    (hij : i ≠ j) :
    ((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j) =
      ((B.card : ℝ) - 1) * (∑ p : Equiv.Perm P, membership B p i) := by
  have hcard : (((Finset.univ : Finset P).erase i).card : ℝ) =
      (Fintype.card P : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Finset.card_erase_add_one (Finset.mem_univ i))
    simp only [Nat.cast_add, Nat.cast_one, Finset.card_univ] at h
    linarith
  have herase :
      (∑ k ∈ (Finset.univ : Finset P).erase i,
        ∑ p : Equiv.Perm P, membership B p i * membership B p k) =
      ((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j) := by
    calc
      _ = ∑ k ∈ (Finset.univ : Finset P).erase i,
          ∑ p : Equiv.Perm P, membership B p i * membership B p j := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_membership_mul_position_eq B (Finset.mem_erase.mp hk).1.symm hij
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  have htotal :
      (∑ k : P, ∑ p : Equiv.Perm P, membership B p i * membership B p k) =
      (B.card : ℝ) * (∑ p : Equiv.Perm P, membership B p i) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_membership]
    rw [← Finset.sum_mul, mul_comm]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset P)
    (fun k => ∑ p : Equiv.Perm P, membership B p i * membership B p k)
    (Finset.mem_univ i)
  rw [herase, htotal] at hsplit
  simp only [membership_sq] at hsplit
  nlinarith

theorem average_membership_mul_of_ne (B : Finset P) {i j : P} (hij : i ≠ j) :
    average (fun p : Equiv.Perm P => membership B p i * membership B p j) =
      (B.card : ℝ) * ((B.card : ℝ) - 1) /
        ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1)) := by
  have hnlarge : 1 < Fintype.card P := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hnlarge' : (1 : ℝ) < Fintype.card P := by exact_mod_cast hnlarge
  have hn : (Fintype.card P : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card P : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card (Equiv.Perm P) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  apply (div_eq_div_iff hp (mul_ne_zero hn hn1)).2
  calc
    _ = (Fintype.card P : ℝ) * (((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j)) := by ring
    _ = (Fintype.card P : ℝ) * (((B.card : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i)) := by
      rw [card_sub_one_mul_sum_membership_mul B hij]
    _ = ((B.card : ℝ) - 1) * ((Fintype.card P : ℝ) *
        (∑ p : Equiv.Perm P, membership B p i)) := by ring
    _ = ((B.card : ℝ) - 1) * ((Fintype.card (Equiv.Perm P) : ℝ) * B.card) := by
      rw [card_mul_sum_membership B i]
    _ = _ := by ring

end MatrixMultiplication.PermutationMatching

end

end OAI
