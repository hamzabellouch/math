import OAI.Combinatorics.Ryser.Incidence.WalkCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem exists_trimmed_many_fourWalks
    (A₀ A : Finset α) (B : Finset β) (G : Finset (α × β))
    (hA₀ : A₀ ⊆ A) (t : ℝ) (ht : 0 ≤ t)
    (hm : 0 < (A₀.card : ℝ))
    (hbad : ((badPairs A₀ B G t).card : ℝ) ≤ (A₀.card : ℝ) ^ 2 / 16) :
    ∃ S : Finset α, S ⊆ A₀ ∧
      3 * (A₀.card : ℝ) / 4 ≤ (S.card : ℝ) ∧
      ∀ a ∈ S, ∀ a' ∈ S,
        (A₀.card : ℝ) / 2 * t ^ 2 ≤ ((fourWalks A B G a a').card : ℝ) := by
  classical
  let m : ℝ := A₀.card
  let R : Finset α := A₀.filter fun a =>
    m / 4 < ((badPartners A₀ B G t a).card : ℝ)
  let S : Finset α := A₀ \ R
  have hRsub : R ⊆ A₀ := Finset.filter_subset _ _
  have htotal : (∑ a ∈ A₀, ((badPartners A₀ B G t a).card : ℝ)) =
      ((badPairs A₀ B G t).card : ℝ) := by
    rw [← Nat.cast_sum, ← card_badPairs_eq_sum_badPartners]
  have hRlower : (R.card : ℝ) * (m / 4) ≤
      ∑ a ∈ R, ((badPartners A₀ B G t a).card : ℝ) := by
    simpa only [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum R
        (fun a => ((badPartners A₀ B G t a).card : ℝ)) (m / 4)
        (fun a ha => le_of_lt (Finset.mem_filter.mp ha).2))
  have hRupper : (∑ a ∈ R, ((badPartners A₀ B G t a).card : ℝ)) ≤
      ((badPairs A₀ B G t).card : ℝ) := by
    calc
      _ ≤ ∑ a ∈ A₀, ((badPartners A₀ B G t a).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hRsub
          (fun a _ _ => Nat.cast_nonneg _)
      _ = _ := htotal
  have hmpos : 0 < m := hm
  have hRcard : (R.card : ℝ) ≤ m / 4 := by
    have hquarter : 0 < m / 4 := by positivity
    apply (mul_le_mul_iff_left₀ hquarter).mp
    have hbound := hRlower.trans (hRupper.trans hbad)
    change (R.card : ℝ) * (m / 4) ≤ m ^ 2 / 16 at hbound
    nlinarith
  have hsplitNat : S.card + R.card = A₀.card :=
    Finset.card_sdiff_add_card_eq_card hRsub
  have hsplit : (S.card : ℝ) + (R.card : ℝ) = m := by
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) hsplitNat
  have hScard : 3 * m / 4 ≤ (S.card : ℝ) := by linarith
  have hkeep (a : α) (ha : a ∈ S) :
      ((badPartners A₀ B G t a).card : ℝ) ≤ m / 4 := by
    apply le_of_not_gt
    intro hgt
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, hgt⟩)
  refine ⟨S, Finset.sdiff_subset, hScard, ?_⟩
  intro a ha a' ha'
  let U : Finset α := badPartners A₀ B G t a ∪ badPartners A₀ B G t a'
  let C : Finset α := A₀ \ U
  have hUsub : U ⊆ A₀ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hUcard : (U.card : ℝ) ≤ m / 2 := by
    have hu : (U.card : ℝ) ≤
        ((badPartners A₀ B G t a).card : ℝ) +
          ((badPartners A₀ B G t a').card : ℝ) := by
      simpa only [Nat.cast_add] using
        (Nat.cast_le.mpr (Finset.card_union_le
          (badPartners A₀ B G t a) (badPartners A₀ B G t a')) :
          (((badPartners A₀ B G t a ∪ badPartners A₀ B G t a').card : ℕ) : ℝ) ≤
            (((badPartners A₀ B G t a).card +
              (badPartners A₀ B G t a').card : ℕ) : ℝ))
    linarith [hkeep a ha, hkeep a' ha']
  have hCsplitNat : C.card + U.card = A₀.card :=
    Finset.card_sdiff_add_card_eq_card hUsub
  have hCsplit : (C.card : ℝ) + (U.card : ℝ) = m := by
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) hCsplitNat
  have hCcard : m / 2 ≤ (C.card : ℝ) := by linarith
  have hCsub : C ⊆ A := Finset.Subset.trans Finset.sdiff_subset hA₀
  have hgood (x : α) (hx : x ∈ C) :
      t ≤ ((commonNeighbors B G a x).card : ℝ) ∧
      t ≤ ((commonNeighbors B G x a').card : ℝ) := by
    have hxA : x ∈ A₀ := (Finset.mem_sdiff.mp hx).1
    have hxU : x ∉ U := (Finset.mem_sdiff.mp hx).2
    constructor
    · apply le_of_not_gt
      intro hlt
      exact hxU (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hxA, hlt⟩)))
    · have hright : t ≤ ((commonNeighbors B G a' x).card : ℝ) := by
        apply le_of_not_gt
        intro hlt
        exact hxU (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hxA, hlt⟩)))
      simpa only [commonNeighbors_comm B G x a'] using hright
  have hwalks : ((fourWalks A B G a a').card : ℝ) =
      ∑ x ∈ A, ((commonNeighbors B G a x).card : ℝ) *
        ((commonNeighbors B G x a').card : ℝ) := by
    rw [card_fourWalks]
    simp only [Nat.cast_sum, Nat.cast_mul]
  calc
    m / 2 * t ^ 2 ≤ (C.card : ℝ) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hCcard (sq_nonneg t)
    _ ≤ ∑ x ∈ C, ((commonNeighbors B G a x).card : ℝ) *
        ((commonNeighbors B G x a').card : ℝ) := by
      simpa only [nsmul_eq_mul] using
        (Finset.card_nsmul_le_sum C
          (fun x => ((commonNeighbors B G a x).card : ℝ) *
            ((commonNeighbors B G x a').card : ℝ)) (t ^ 2) (by
              intro x hx
              rw [pow_two]
              exact mul_le_mul (hgood x hx).1 (hgood x hx).2 ht (Nat.cast_nonneg _)))
    _ ≤ ∑ x ∈ A, ((commonNeighbors B G a x).card : ℝ) *
        ((commonNeighbors B G x a').card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hCsub
        (fun x _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = ((fourWalks A B G a a').card : ℝ) := hwalks.symm

end RyserCoveringCounterexample.Incidence

end OAI
