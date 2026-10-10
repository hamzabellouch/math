import OAI.NumberTheory.TwoPoint.Walks.ColumnSingletonDecay
import OAI.NumberTheory.TwoPoint.Walks.ColumnManyUnlitDecay
import OAI.NumberTheory.TwoPoint.Walks.ColumnHighRankTraceTotal
import OAI.NumberTheory.TwoPoint.Bounds.GoodTraceTotal
import OAI.NumberTheory.TwoPoint.Bounds.TraceFourBounds

namespace OAI

/-! All four contributions to the literal centered trace on a single
column/padding catalog, with the full external dimension allowance retained. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_column_trace_total (h : ℕ) (C Ce Cs Cw W : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B s D k n K₀ H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
      (_hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
      (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → ℝ)
      (A external : ℝ) (cut : Fin (2 * k))
      (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
      (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((⌊L ^ (1 / 4 : ℝ)⌋₊ + 2 * k * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((2 * k * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      ((2 * k : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ j, P j ⊆ data.P) →
      (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ j, primeHarmonicMass (P j) ≤ L ^ (2 : ℕ)) →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (Qmax : ℝ) ≤ Real.exp (100 * L + 1) → (Dmax : ℝ) ≤ Real.exp (2 * L) →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, (a.2 i).val ≤ Qmax) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ Dmax) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ A → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, cap a * 2 ^ (2 * k * J + (singletonLabels (label a)).card) ≤ A) →
      (∀ a ∈ F, (singletonLabels (label a)).card ≤ ⌊L ^ (1 / 4 : ℝ)⌋₊ →
        cap a * 2 ^ (singletonLabels (label a)).card ≤
        crudeTraceWeight (2 * k) ⌊L ^ (1 / 4 : ℝ)⌋₊ (fun i => (a.2 i).val) L external) →
      (∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) → weight a x = weight a y) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      2 * k + n * s ≤ D →
      (∀ a ∈ F, ⌊L ^ (1 / 4 : ℝ)⌋₊ < (singletonLabels (label a)).card →
        n * (s * J) < (singletonLabels (label a)).card) →
      (D : ℝ) ≤ 4 * L → 0 < n → (n : ℝ) ≤ 4 * L → 8 * K₀ ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K₀ : ℝ) → (K₀ : ℝ) ≤ L →
      0 < h → 0 < s → L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      0 ≤ K → (∀ q, 0 ≤ u q) →
      (∀ a ∈ F, ∀ x, weight a x ≤
        retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) →
      Real.exp (108 * L) * (∑ a ∈ F, |prohibitedCenteredAverage data hB s D
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) (weight a)|) ≤
        Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
          2 * Real.exp (-L ^ (101 / 100 : ℝ))) +
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_prohibited_column_singleton_decay C Cw hC hCw,
    eventually_prohibited_column_many_unlit_decay C Ce Cs hC hCe hCs,
    eventually_prohibited_column_high_rank_total h C C Cw hC hC hCw,
    eventually_prohibited_good_trace_total W hW, eventually_ge_atTop (0 : ℝ)]
    with L hsingle hunlit hrank hgood hL
  intro J M B s D k n K₀ H Y Qmax Dmax data hB P Q F hR forward label base weight cap
    A external cut u eligible g K extra next origin hJ hklo hkhi hJM hS hslots hRp
    hP hVm hVM hVpoly hmass hPmass hQmass hM hprime hdisjoint hlo hhi hY hYexp hH
    hQmax hDmax hpairs hq hd hlabel hA hAexp hext hextL hcap hw hwcap hcost hcrude
    hdep hpadding hD hn hDL hnpos hnL hKn hKlo hKhi hh hs hsL hleft hright hK hu hpad
  let word (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    columnTupleWord a.1 forward (fun i => (a.2 i).val)
  let large := F.filter (fun a => ⌊L ^ (1 / 4 : ℝ)⌋₊ < (singletonLabels (label a)).card)
  let small := F.filter (fun a => (singletonLabels (label a)).card ≤ ⌊L ^ (1 / 4 : ℝ)⌋₊)
  let bad (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
      (U : Finset (Fin (2 * k) × Fin J)) := ∃ j, ¬ColumnLowRank
    (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
    hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊
  have hlarge : large ⊆ F := filter_subset _ _
  have hsmall : small ⊆ F := filter_subset _ _
  have hRL : ((2 * k : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith
  have hJC : (J : ℝ) ≤ C * Real.log L := by
    have : (J : ℝ) ≤ (J + M : ℕ) := by exact_mod_cast Nat.le_add_right J M
    exact this.trans hJM
  have hMC : (M : ℝ) ≤ C * Real.log L := by
    have : (M : ℝ) ≤ (J + M : ℕ) := by exact_mod_cast Nat.le_add_left M J
    exact this.trans hJM
  have hRM : ((2 * k * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    apply le_trans _ hslots
    have : 2 * k * M ≤ 2 * k * (J + M) := Nat.mul_le_mul_left _ (Nat.le_add_left M J)
    exact_mod_cast Nat.add_le_add_right this 1
  have hsbound := hsingle h J M (2 * k) B s n D K₀ H Y data hB P Q forward large label base
    weight cap A hprime hdisjoint hA (fun a ha => hcap a (hlarge ha))
    (fun a ha => hw a (hlarge ha)) (fun a ha => hwcap a (hlarge ha))
    (fun a ha => hcost a (hlarge ha)) (fun a ha => hdep a (hlarge ha))
    (fun a ha => hpadding a (hlarge ha)) (fun a ha => hpairs a (hlarge ha))
    (fun a ha => hlabel a (hlarge ha)) hD (fun a ha => hn a (hlarge ha) (mem_filter.mp ha).2)
    hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hY hYexp hlo hhi hH hAexp
  have hubound := hunlit (2 * k) J M ⌊L ^ (1 / 4 : ℝ)⌋₊ B h s D data hB P Q forward small
    label base weight cap external H hprime hdisjoint hR hRL hS hJM hslots hRp
    hext hextL hPmass hQmass hM hH (fun p hp => by exact_mod_cast hlo p hp)
    (fun a ha => hpairs a (hsmall ha)) (fun a ha => hlabel a (hsmall ha))
    (fun a ha => hcap a (hsmall ha)) (fun a ha => hw a (hsmall ha))
    (fun a ha => hwcap a (hsmall ha)) (fun a ha => hpadding a (hsmall ha))
    (fun a ha => hcrude a (hsmall ha) (mem_filter.mp ha).2)
  have hrcost (a) (ha : a ∈ F) : cap a * 2 ^ (singletonLabels (label a)).card ≤ A := by
    apply le_trans _ (hcost a ha)
    apply mul_le_mul_of_nonneg_left _ (hcap a ha)
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega)
  have hrbound := hrank J (2 * k) M Qmax Dmax Y H B s D data hB P Q F forward cut label
    base weight cap A hR hRL hJC hMC hRM hRp hP hVpoly hQmass hVm hprime hdisjoint
    hlo hhi hQmax hDmax hYexp hH hpairs hq hd hlabel hA hAexp hcap hw hwcap hpadding hrcost
  let good : ℝ := ∑ a ∈ small, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
    (fun U => U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ¬bad a U),
    prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U
  have hgbound : Real.exp (108 * L) * good ≤
      (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
    have hb := hgood h J M B s D k ⌊L ^ (1 / 4 : ℝ)⌋₊ data hB P Q small hR forward
      label base weight cut u eligible g K extra next origin hJ hklo hkhi
      (Nat.floor_le (Real.rpow_nonneg hL _)) hprime hdisjoint
      (fun a ha => hpairs a (hsmall ha)) (by omega) (fun a ha => hlabel a (hsmall ha))
      (fun a ha => hdep a (hsmall ha)) (fun a ha => hpadding a (hsmall ha)) hh hs hsL
      (fun a ha => hleft a (hsmall ha)) (fun a ha => hright a (hsmall ha)) hK hu hVM
      (by
        intro a ha
        rw [← tuple_label_singleton_count a.1 hdisjoint Subtype.val Subtype.val_injective
          (label a) (hlabel a (hsmall ha))]
        exact (mem_filter.mp ha).2)
      (fun a ha => hw a (hsmall ha)) (fun a ha => hpad a (hsmall ha))
    convert hb using 1
    congr 1
    apply sum_congr rfl
    intro a _
    apply sum_congr
    · ext U
      constructor
      · intro hU
        obtain ⟨hmem, hcard, hbad⟩ := mem_filter.mp hU
        apply mem_filter.mpr
        refine ⟨hmem, hcard, ?_⟩
        intro j
        by_contra hj
        exact hbad ⟨j, hj⟩
      · intro hU
        obtain ⟨hmem, hcard, hlow⟩ := mem_filter.mp hU
        apply mem_filter.mpr
        refine ⟨hmem, hcard, ?_⟩
        rintro ⟨j, hj⟩
        exact hj (hlow j)
    · intro U _
      rfl
  have hb := prohibited_trace_four_bounds data hB s D F word label base weight hw hdep
    ⌊L ^ (1 / 4 : ℝ)⌋₊ ⌊L ^ (1 / 50 : ℝ)⌋₊ bad
    (Real.exp (-L ^ (21 / 20 : ℝ))) (Real.exp (-L ^ (101 / 100 : ℝ)))
    (Real.exp (-L ^ (101 / 100 : ℝ))) good hsbound hubound
    (by
      convert hrbound using 1
      apply sum_congr rfl
      intro a _
      apply sum_congr
      · dsimp only [bad]
        exact filter_congr_decidable _ _ _
      · intro U _
        rfl)
    (by
      dsimp only [good, small]
      apply le_of_eq
      apply sum_congr
      · exact filter_congr_decidable _ _ _
      · intro a _
        apply sum_congr
        · exact filter_congr_decidable _ _ _
        · intro U _
          rfl)
  calc
    _ ≤ Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        Real.exp (-L ^ (101 / 100 : ℝ)) + Real.exp (-L ^ (101 / 100 : ℝ)) + good) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) + Real.exp (108 * L) * good := by ring
    _ ≤ _ := add_le_add le_rfl hgbound

end TwoPointCorrelations

end OAI
