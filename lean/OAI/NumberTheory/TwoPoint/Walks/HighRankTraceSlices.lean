import OAI.NumberTheory.TwoPoint.Walks.ProhibitedHighRankDecay

namespace OAI

/-! Sum the actual variable perfect-row and offending-column choices by fixed
rank slices.  Only finite positive sums are enlarged. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def highRankTraceSlice {J R : ℕ} {P : Fin J → Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → ι)
    (forward : Fin R → Bool) (hR : 0 < R) (h r : ℕ) (cut : Fin R)
    (U : Finset (Fin R × Fin J)) (perfect : Finset (Fin R)) (j : Fin J) :=
  F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ perfectRows (label a) U = perfect ∧
    ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j) hR h perfect cut r)

theorem prohibited_high_rank_sum_le_slices {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D r : ℕ) (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      Fin R × Fin J → ↥(data.P ∪ data.Q))
    (forward : Fin R → Bool) (hR : 0 < R) (cut : Fin R)
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j)
        hR h (perfectRows (label a) U) cut r),
      prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
        (label a) base (weight a) U) ≤
      ∑ U : Finset (Fin R × Fin J), ∑ perfect : Finset (Fin R), ∑ j : Fin J,
        ∑ a ∈ highRankTraceSlice F label forward hR h r cut U perfect j,
          prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
            (label a) base (weight a) U := by
  let T a U := prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
    (label a) base (weight a) U
  let S a U perfect j := U ⊆ nonsingletonSlots (label a) ∧
    perfectRows (label a) U = perfect ∧
    ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j) hR h perfect cut r
  have hT a (ha : a ∈ F) U : 0 ≤ T a U :=
    prohibitedDesignatedTerm_nonneg data hB s D _ _ base _ (hw a ha) U
  have hnonneg a (ha : a ∈ F) U perfect j :
      0 ≤ if S a U perfect j then T a U else 0 := by
    split_ifs
    · exact hT a ha U
    · exact le_rfl
  have hpoint a (ha : a ∈ F) U (hU : U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j)
        hR h (perfectRows (label a) U) cut r)) :
      T a U ≤ ∑ perfect : Finset (Fin R), ∑ j : Fin J, if S a U perfect j then T a U else 0 := by
    obtain ⟨hU, j, hj⟩ := mem_filter.mp hU
    have hs : S a U (perfectRows (label a) U) j := ⟨mem_powerset.mp hU, rfl, hj⟩
    calc
      T a U = if S a U (perfectRows (label a) U) j then T a U else 0 := (ite_eq_left hs).symm
      _ ≤ ∑ j : Fin J, if S a U (perfectRows (label a) U) j then T a U else 0 :=
        single_le_sum (f := fun j => if S a U (perfectRows (label a) U) j then T a U else 0)
          (fun j _ => hnonneg a ha U _ j) (mem_univ j)
      _ ≤ _ := single_le_sum
        (f := fun perfect => ∑ j : Fin J, if S a U perfect j then T a U else 0)
        (fun perfect _ => sum_nonneg (fun j _ => hnonneg a ha U perfect j))
        (mem_univ (perfectRows (label a) U))
  calc
    _ ≤ ∑ a ∈ F, ∑ U : Finset (Fin R × Fin J), ∑ perfect : Finset (Fin R), ∑ j : Fin J,
        if S a U perfect j then T a U else 0 := by
      apply sum_le_sum
      intro a ha
      apply (sum_le_sum (fun U hU => hpoint a ha U hU)).trans
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro U _ _
      exact sum_nonneg (fun perfect _ => sum_nonneg (fun j _ => hnonneg a ha U perfect j))
    _ = _ := by
      simp only [highRankTraceSlice, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro U _
      rw [sum_comm]
      apply sum_congr rfl
      intro perfect _
      rw [sum_comm]

theorem prohibited_high_rank_sum_le_uniform_slices {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D r : ℕ) (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      Fin R × Fin J → ↥(data.P ∪ data.Q))
    (forward : Fin R → Bool) (hR : 0 < R) (cut : Fin R)
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x) (E : ℝ)
    (hE : ∀ U perfect j,
      (∑ a ∈ highRankTraceSlice F label forward hR h r cut U perfect j,
        prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
          (label a) base (weight a) U) ≤ E) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j)
        hR h (perfectRows (label a) U) cut r),
      prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
        (label a) base (weight a) U) ≤ (2 : ℝ) ^ (R * J) * 2 ^ R * J * E := by
  apply (prohibited_high_rank_sum_le_slices data hB s D r F label forward hR cut base weight hw).trans
  calc
    _ ≤ ∑ _U : Finset (Fin R × Fin J), ∑ _perfect : Finset (Fin R), ∑ _j : Fin J, E :=
      sum_le_sum (fun U _ => sum_le_sum (fun perfect _ => sum_le_sum (fun j _ => hE U perfect j)))
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      ring

end TwoPointCorrelations

end OAI
