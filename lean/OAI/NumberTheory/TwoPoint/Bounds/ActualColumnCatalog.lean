import OAI.NumberTheory.TwoPoint.Bounds.ActualColumnWeights

namespace OAI

/-! Structural properties of the column fiber of actual closed matrix paths. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma singletonLabels_card_le_slots {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] (label : τ → ι) :
    (singletonLabels label).card ≤ Fintype.card τ := by
  rw [← singleton_slot_count label]
  exact (card_le_card (filter_subset _ _)).trans_eq (card_univ)

variable {h J M k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V]

omit [Fintype V] in
lemma actualColumnCatalog_pairs (data : ProhibitedPrimeFamily h J M)
    (embed : V → ((j : Fin J) → P j) × ℤ) (Q : Finset ℕ)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q
      (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward)
    (i : Fin (2 * k)) : (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs := by
  obtain ⟨p, hp, hw⟩ := closedTraceFiber_word Q _ forward a ha
  have hs := (mem_filter.mp hp).2.2
  apply hs (SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val)
  rw [← hw]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma actualColumnCatalog_chains (data : ProhibitedPrimeFamily h J M)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (embed : V → ((j : Fin J) → P j) × ℤ) (Q : Finset ℕ)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q
      (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward) :
    ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take k).IsChain
        (fun a b => a.tuple ≠ b.tuple) ∧
      ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop k).IsChain
        (fun a b => a.tuple ≠ b.tuple) := by
  obtain ⟨p, hp, hw⟩ := closedTraceFiber_word Q _ forward a ha
  rw [hw]
  exact actualClosedPairCatalog_chains embed Q _ (primeTuple_injective hprime hdisjoint)
    gate data.pairs x p hp

omit [Fintype V] in
lemma actualColumnCatalog_crude_cost (data : ProhibitedPrimeFamily h J M)
    (hP : ∀ j, P j ⊆ data.P) (L C : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hk : (k : ℝ) ≤ L)
    (hJ : (J : ℝ) ≤ C * Real.log L) (hM : (M : ℝ) ≤ 100 * Real.log L)
    (embed : V → ((j : Fin J) → P j) × ℤ) (Q : Finset ℕ)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q
      (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward) :
    columnCrudeCap L a * 2 ^ (2 * k * J + (singletonLabels (actualColumnLabel data hP a.1)).card) ≤
      Real.exp ((4 * C + 402) * L * (Real.log L) ^ 2) := by
  have hs : (singletonLabels (actualColumnLabel data hP a.1)).card ≤ 2 * k * J := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      singletonLabels_card_le_slots (actualColumnLabel data hP a.1)
  apply columnCrudeCap_exp L (4 * C) a hL hlog (by push_cast; linarith)
  · have hs' : ((singletonLabels (actualColumnLabel data hP a.1)).card : ℝ) ≤ 2 * k * J := by
      exact_mod_cast hs
    have hp := mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hJ
      (show (0 : ℝ) ≤ J by positivity) (show 0 ≤ 2 * L by positivity)
    push_cast
    nlinarith
  · intro i
    exact (show (((a.2 i).val).primeFactors.card : ℝ) ≤ M by
      exact_mod_cast data.padding_card _
        (actualColumnCatalog_pairs data embed Q gate x forward a ha i)).trans hM

end TwoPointCorrelations

end OAI
