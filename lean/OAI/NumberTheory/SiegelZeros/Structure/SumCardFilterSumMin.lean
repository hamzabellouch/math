import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Selection.GreedyPivots

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets

open scoped BigOperators

theorem sum_card_filter_lt_eq_sum_min {ι : Type*} (s : Finset ι) (a : ι → ℕ) (T : ℕ) :
    (∑ k ∈ Finset.range T, (s.filter fun i => k < a i).card) =
      ∑ i ∈ s, min T (a i) := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.card_filter]
  have h : (Finset.range T).filter (fun k => k < a i) = Finset.range (min T (a i)) := by
    ext k
    simp [lt_min_iff]
  rw [h, Finset.card_range]

theorem sum_range_div_le_of_bounded_multiplicity {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (Q : ℕ) (hQpos : 0 < Q)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (∑ i ∈ Finset.range s.card, i / Q) ≤ ∑ i ∈ s, a i := by
  classical
  have htail (k : ℕ) :
      ((Finset.range s.card).filter fun i => k < i / Q).card ≤
        (s.filter fun i => k < a i).card := by
    have hlow : ((Finset.range s.card).filter fun i => i / Q ≤ k).card =
        min s.card ((k + 1) * Q) := by
      have hset : (Finset.range s.card).filter (fun i => i / Q ≤ k) =
          Finset.range (min s.card ((k + 1) * Q)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
        rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hQpos]
      rw [hset, Finset.card_range]
    have hsmall : (s.filter fun i => a i ≤ k).card ≤ min s.card ((k + 1) * Q) := by
      apply le_min (Finset.card_filter_le _ _)
      simpa [Nat.lt_succ_iff, Nat.mul_comm] using card_filter_lt_le_mul s a Q (k + 1) hQ
    have hc := Finset.card_filter_add_card_filter_not (s := s) (fun i => a i ≤ k)
    have hd := Finset.card_filter_add_card_filter_not (s := Finset.range s.card)
      (fun i => i / Q ≤ k)
    simp only [not_le, Finset.card_range] at hc hd
    omega
  calc
    _ = ∑ i ∈ Finset.range s.card, min s.card (i / Q) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (min_eq_right ((Nat.div_le_self i Q).trans (Finset.mem_range.mp hi).le)).symm
    _ = ∑ k ∈ Finset.range s.card,
        ((Finset.range s.card).filter fun i => k < i / Q).card :=
      (sum_card_filter_lt_eq_sum_min (Finset.range s.card) (fun i => i / Q) s.card).symm
    _ ≤ ∑ k ∈ Finset.range s.card, (s.filter fun i => k < a i).card :=
      Finset.sum_le_sum fun k _ => htail k
    _ = ∑ i ∈ s, min s.card (a i) := sum_card_filter_lt_eq_sum_min s a s.card
    _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum fun i _ => min_le_right _ _

theorem filling_order_minimizes_sum (M Q : ℕ) (hQ : 0 < Q) :
    (∀ k, ((Finset.range M).filter fun i => i / Q = k).card ≤ Q) ∧
      ∀ a : ℕ → ℕ, (∀ k, ((Finset.range M).filter fun i => a i = k).card ≤ Q) →
        (∑ i ∈ Finset.range M, i / Q) ≤ ∑ i ∈ Finset.range M, a i := by
  classical
  constructor
  · intro k
    have h := Finset.card_le_card_of_injOn
      (s := (Finset.range M).filter fun i => i / Q = k) (t := Finset.range Q)
      (fun i => i % Q) ?_ ?_
    · simpa using h
    · intro i _
      exact Finset.mem_range.mpr (Nat.mod_lt i hQ)
    · intro i hi j hj hij
      change i % Q = j % Q at hij
      exact (Nat.ext_div_mod_iff Q i j).mpr
        ⟨(Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm, hij⟩
  · intro a ha
    simpa using sum_range_div_le_of_bounded_multiplicity (Finset.range M) a Q hQ ha

end WeightedTorusJets

end

end SiegelZeros

end OAI
