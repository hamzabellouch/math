import OAI.NumberTheory.TwoPoint.Bounds.TraceDesignationSlices
import OAI.NumberTheory.TwoPoint.Bounds.GoodTraceCost

namespace OAI

/-! All good designated terms, including the finite choice of designation, fit
inside the absolute square-root harmonic-mass moment bound. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_good_trace_total (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M B s D k S : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
      (hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
      (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cut : Fin (2 * k))
      (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
      (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      2 * k ≤ D → (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      (∀ a ∈ F, ∀ y z, (∀ i, i ∉ univ.image (label a) → y i = z i) → weight a y = weight a z) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      0 < h → 0 < s → L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      0 ≤ K → (∀ q, 0 ≤ u q) → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ a ∈ F, columnSingletonCount a.1 ≤ S) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤
        retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) →
      Real.exp (108 * L) *
        (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ∀ j, ColumnLowRank
            (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
            hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
          prohibitedDesignatedTerm data hB s D
            (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base (weight a) U) ≤
      (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_tuple_perfectRows_budget,
    eventually_good_trace_cost W hW] with L hL hbudget hcost
  intro h J M B s D k S data hB P Q F hR forward label base weight cut u eligible g K extra next origin
    hJ hklo hkhi hS hprime hdisjoint hpairs hRD hlabel hweight hpadding hh hs hsL
    hleft hright hK hu hmass hsingle hw hpad
  let word (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    columnTupleWord a.1 forward (fun i => (a.2 i).val)
  let keep (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
      (U : Finset (Fin (2 * k) × Fin J)) := U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ∀ j, ColumnLowRank
    (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
    hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊
  let A := (2 : ℝ) ^ (2 * S) * ((Fintype.card (BudgetColumnArrayCode J (4 * k) L) : ℝ) *
    K ^ (2 * k) * (2 * W) ^ (J * k + S))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hslice (U : Finset (Fin (2 * k) × Fin J)) :
      (∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
        prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ A := by
    let E := (F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U)).filter
      (fun a => LitConsistent (nonsingletonSlots (label a) \ U) (label a)
        (tupleForcedTarget data hB (word a) (label a)))
    have hEF : E ⊆ F := (filter_subset _ _).trans (filter_subset _ _)
    rw [prohibited_designated_sum_eq_lit_filter]
    apply good_designated_word_sum data hB P Q E hR forward hprime hdisjoint
      (fun a ha => hpairs a (hEF ha)) hRD label (fun a ha => hlabel a (hEF ha)) base U
      (fun _ ha => (mem_filter.mp (mem_filter.mp ha).1).2.1)
      (fun _ ha => (mem_filter.mp ha).2) weight
      (fun a ha => hweight a (hEF ha)) (fun a ha => hpadding a (hEF ha)) hh hs cut
      (fun a ha => hleft a (hEF ha)) (fun a ha => hright a (hEF ha))
      L K (2 * W) hL (by exact_mod_cast (mul_le_mul_of_nonneg_left hkhi (by norm_num : (0 : ℝ) ≤ 2)))
      hsL (Nat.floor_le (Real.rpow_nonneg (by linarith) _)) ?_ ?_
      u eligible g extra next origin hK (by linarith) hu hmass
      (fun a ha => (hsingle a (hEF ha)).trans (by omega))
      (fun a ha => hw a (hEF ha)) (fun a ha => hpad a (hEF ha))
    · intro a ha
      rw [tuple_label_perfectRows a.1 hdisjoint _ Subtype.val_injective _ (hlabel a (hEF ha))]
      apply hbudget J (2 * k) P a.1 U cut
      · exact (show (columnSingletonCount a.1 : ℝ) ≤ S by exact_mod_cast hsingle a (hEF ha)).trans hS
      · exact (show (U.card : ℝ) ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ by
          exact_mod_cast (mem_filter.mp (mem_filter.mp ha).1).2.2.1).trans
          (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    · intro a ha
      exact (mem_filter.mp (mem_filter.mp ha).1).2.2.2
  have htotal := prohibited_designation_sum_le data hB s D F word label base weight keep A
    (by
      intro U
      convert hslice U using 1
      apply sum_congr
      · ext a
        simp only [mem_filter]
      · intro a _
        rfl)
  have hexp : 2 * k * J ≤ 4 * k * J :=
    Nat.mul_le_mul_right J (Nat.mul_le_mul_right k (by decide : 2 ≤ 4))
  have htotal' := htotal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp) hA)
  convert (mul_le_mul_of_nonneg_left htotal' (Real.exp_pos (108 * L)).le).trans
    (by simpa only [mul_assoc] using hcost J k S K A hJ hklo hkhi hS hK le_rfl) using 1
  congr 1
  apply sum_congr rfl
  intro a _
  apply sum_congr
  · ext U
    simp only [mem_filter, keep]
  · intro U _
    rfl

end TwoPointCorrelations

end OAI
