import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

section DoubleCounting

variable {P L : Type*} [Fintype L]
variable (I : P → L → Prop) [DecidableRel I]

theorem sum_line_count_eq_sum_point_count (U : Finset P) :
    (∑ l : L, (U.filter fun p => I p l).card) =
      ∑ p ∈ U, ((Finset.univ : Finset L).filter fun l => I p l).card := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := I) (s := U) (t := Finset.univ)).symm

theorem sum_line_count (U : Finset P) (r : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = r) :
    (∑ l : L, (U.filter fun p => I p l).card) = r * U.card := by
  rw [sum_line_count_eq_sum_point_count]
  calc
    (∑ p ∈ U, ((Finset.univ : Finset L).filter fun l => I p l).card) =
        ∑ _p ∈ U, r := Finset.sum_congr rfl hpoint
    _ = r * U.card := by simp [Nat.mul_comm]

theorem sum_sq_line_count_eq_sum_pair_count (U : Finset P) :
    (∑ l : L, (U.filter fun p => I p l).card ^ 2) =
      ∑ p ∈ U, ∑ p' ∈ U,
        ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card := by
  classical
  have hline (l : L) :
      (U.filter fun p => I p l).card ^ 2 =
        ∑ p ∈ U, ∑ p' ∈ U, if I p l ∧ I p' l then 1 else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro p' hp'
    by_cases h : I p l <;> by_cases h' : I p' l <;> simp [h, h']
  simp_rw [hline]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p' hp'
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_sq_line_count (U : Finset P) (q : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = q + 1)
    (hpair : ∀ p ∈ U, ∀ p' ∈ U, p ≠ p' →
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card = 1) :
    (∑ l : L, (U.filter fun p => I p l).card ^ 2) =
      U.card ^ 2 + q * U.card := by
  classical
  rw [sum_sq_line_count_eq_sum_pair_count]
  have hcommon (p : P) (hp : p ∈ U) (p' : P) (hp' : p' ∈ U) :
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card =
        1 + if p' = p then q else 0 := by
    by_cases h : p' = p
    · subst p'
      simp [hpoint p hp, Nat.add_comm]
    · simp [h, hpair p hp p' hp' (Ne.symm h)]
  calc
    (∑ p ∈ U, ∑ p' ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card) =
        ∑ p ∈ U, ∑ p' ∈ U, (1 + if p' = p then q else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro p' hp'
          exact hcommon p hp p' hp'
    _ = ∑ p ∈ U, (U.card + q) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [Finset.sum_add_distrib, hp]
    _ = U.card ^ 2 + q * U.card := by
      simp only [Finset.sum_const, smul_eq_mul]
      ring

theorem common_line_count_of_existsUnique (p p' : P)
    (h : ∃! l : L, I p l ∧ I p' l) :
    ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card = 1 := by
  classical
  obtain ⟨l, hl, hunique⟩ := h
  apply Finset.card_eq_one.mpr
  refine ⟨l, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hk => hunique k hk, fun hk => hk ▸ hl⟩

theorem sum_sq_line_count_of_unique (U : Finset P) (q : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = q + 1)
    (hpair : ∀ p ∈ U, ∀ p' ∈ U, p ≠ p' → ∃! l : L, I p l ∧ I p' l) :
    (∑ l : L, (U.filter fun p => I p l).card ^ 2) =
      U.card ^ 2 + q * U.card := by
  apply sum_sq_line_count I U q hpoint
  intro p hp p' hp' hne
  exact common_line_count_of_existsUnique I p p' (hpair p hp p' hp' hne)

theorem sum_line_count_real (U : Finset P) (q : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = q + 1) :
    (∑ l : L, ((U.filter fun p => I p l).card : ℝ)) =
      ((q : ℝ) + 1) * (U.card : ℝ) := by
  exact_mod_cast sum_line_count I U (q + 1) hpoint

theorem sum_sq_line_count_real (U : Finset P) (q : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = q + 1)
    (hpair : ∀ p ∈ U, ∀ p' ∈ U, p ≠ p' →
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card = 1) :
    (∑ l : L, ((U.filter fun p => I p l).card : ℝ) ^ 2) =
      (U.card : ℝ) ^ 2 + (q : ℝ) * (U.card : ℝ) := by
  exact_mod_cast sum_sq_line_count I U q hpoint hpair

end DoubleCounting

end Balanced

end OAI
