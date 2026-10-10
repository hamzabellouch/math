import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

def purposefulIndices {b κ : ℕ} (P : EqualityPattern b κ)
    (c : Fin (4 * b - κ)) : Finset (Fin b × Fin 4) :=
  Finset.univ.filter (fun ij =>
    P.classOf ij.1 ij.2 = c ∨ P.classOf ij.1 (ij.2 + 1) = c)

theorem purposeful_positions_card_le {α : Type*} [DecidableEq α] (f : Fin 4 → α)
    (hf : Function.Injective f) (c : α) :
    (Finset.univ.filter (fun i => f i = c ∨ f (i + 1) = c)).card ≤
      if ∃ i, f i = c then 2 else 0 := by
  by_cases hc : ∃ i, f i = c
  · simp only [hc, ite_true]
    obtain ⟨j, hj⟩ := hc
    have hsub : Finset.univ.filter (fun i => f i = c ∨ f (i + 1) = c) ⊆
        {j, j - 1} := by
      intro i hi
      obtain hi | hi := (Finset.mem_filter.mp hi).2
      · exact Finset.mem_insert.mpr (Or.inl (hf (hi.trans hj.symm)))
      · have hnext : i + 1 = j := hf (hi.trans hj.symm)
        have hprev : i = j - 1 := (eq_sub_iff_add_eq).mpr hnext
        simp [hprev]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp only [hc, ite_false]
    apply Nat.le_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain hi | hi := (Finset.mem_filter.mp hi).2
    · exact hc ⟨i, hi⟩
    · exact hc ⟨i + 1, hi⟩

theorem purposeful_positions_card_eq {α : Type*} [DecidableEq α] (f : Fin 4 → α)
    (hf : Function.Injective f) (c : α) :
    (Finset.univ.filter (fun i => f i = c ∨ f (i + 1) = c)).card =
      if ∃ i, f i = c then 2 else 0 := by
  apply le_antisymm (purposeful_positions_card_le f hf c)
  by_cases hc : ∃ i, f i = c
  · simp only [hc, ite_true]
    obtain ⟨j, hj⟩ := hc
    have hne : j ≠ j - 1 := by fin_cases j <;> decide
    have hcard : ({j, j - 1} : Finset (Fin 4)).card = 2 := by simp [hne]
    rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hj⟩
    · have hi' : i = j - 1 := Finset.mem_singleton.mp hi
      subst i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr (by simpa only [sub_add_cancel] using hj)⟩
  · simp only [hc, ite_false]
    exact Nat.zero_le _

theorem purposefulIndices_card_le {b κ : ℕ} (P : EqualityPattern b κ)
    (c : Fin (4 * b - κ)) :
    (purposefulIndices P c).card ≤
      2 * (Finset.univ.filter (fun i => ∃ j, P.classOf i j = c)).card := by
  have hsum : (purposefulIndices P c).card =
      ∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        P.classOf i j = c ∨ P.classOf i (j + 1) = c)).card := by
    simp only [purposefulIndices, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  calc
    (∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        P.classOf i j = c ∨ P.classOf i (j + 1) = c)).card) ≤
        ∑ i : Fin b, if ∃ j, P.classOf i j = c then 2 else 0 :=
      Finset.sum_le_sum (fun i _ => purposeful_positions_card_le
        (P.classOf i) (P.withinTuple i) c)
    _ = 2 * (Finset.univ.filter (fun i => ∃ j, P.classOf i j = c)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

def purposefulDirections {F : Type*} [DecidableEq F] {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (d : Direction F) : Finset (Fin b × Fin 4) :=
  Finset.univ.filter (fun ij =>
    a.2 (P.classOf ij.1 ij.2) = d ∨ a.2 (P.classOf ij.1 (ij.2 + 1)) = d)

theorem purposefulDirections_card_le {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (ha : Function.Injective a.2) (d : Direction F) :
    (purposefulDirections P a d).card ≤
      2 * (Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)).card := by
  have hsum : (purposefulDirections P a d).card =
      ∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        a.2 (P.classOf i j) = d ∨ a.2 (P.classOf i (j + 1)) = d)).card := by
    simp only [purposefulDirections, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  calc
    (∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        a.2 (P.classOf i j) = d ∨ a.2 (P.classOf i (j + 1)) = d)).card) ≤
        ∑ i : Fin b, if ∃ j, a.2 (P.classOf i j) = d then 2 else 0 :=
      Finset.sum_le_sum (fun i _ => purposeful_positions_card_le
        (fun j => a.2 (P.classOf i j)) (ha.comp (P.withinTuple i)) d)
    _ = 2 * (Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

theorem purposefulDirections_card_eq {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (ha : Function.Injective a.2) (d : Direction F) :
    (purposefulDirections P a d).card =
      2 * (Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)).card := by
  have hsum : (purposefulDirections P a d).card =
      ∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        a.2 (P.classOf i j) = d ∨ a.2 (P.classOf i (j + 1)) = d)).card := by
    simp only [purposefulDirections, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  simp_rw [purposeful_positions_card_eq
    (fun j => a.2 (P.classOf _ j)) (ha.comp (P.withinTuple _)) d]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end
end Balanced.Local.Surplus

end OAI
