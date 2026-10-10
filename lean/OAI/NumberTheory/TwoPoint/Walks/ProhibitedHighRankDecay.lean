import OAI.NumberTheory.TwoPoint.Walks.HighRankWeightedWords
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms
import OAI.NumberTheory.TwoPoint.Bounds.SuppliedTupleWords
import OAI.NumberTheory.TwoPoint.Walks.TupleLitOrigins

namespace OAI

/-! The high-rank estimate for the literal designated trace terms.  Common integer
origins and all prime-support conditions follow from the supplied words. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_high_rank_decay (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Q D Y H Z s N : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hZ : ∀ p ∈ data.P ∪ data.Q, p ≤ Z)
      (P : Fin J → Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin Z) (U : Finset (Fin R × Fin J))
      (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        (↥(data.P ∪ data.Q) → Fin Z) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, P l ⊆ data.P) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ l, ∀ p ∈ P l, p.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, a.2 i) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      (∀ a ∈ F, perfect ⊆ perfectRows (label a) U) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, U ⊆ nonsingletonSlots (label a)) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        MainPaddingTests Subtype.val h Z (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, prohibitedDesignatedTerm data hZ s N
        (columnTupleWord a.1 forward a.2) (label a) base (weight a) U) ≤
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_weighted_high_rank_words h Cj Cm Cw hCj hCm hCw] with L hdecay
  intro J R M Q D Y H Z s N data hZ P F forward j perfect cut label base U weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
    hpairs hq hd hrank hlabel hperfect hW hWexp hU hcap hw hwcap hpadding hcost
  let E := F.filter (fun a => LitConsistent (nonsingletonSlots (label a) \ U) (label a)
    (tupleForcedTarget data hZ (columnTupleWord a.1 forward a.2) (label a)))
  have hEF : E ⊆ F := filter_subset _ _
  obtain ⟨origin, horigin⟩ := ambient_tuple_lit_origins E
    (fun a => a.1) Z Subtype.val data.prime Subtype.val_injective
    (fun p => hZ _ p.property) label (fun a ha => hlabel a (hEF ha)) U
    (fun a i => wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val))
    base perfect (fun a ha => hperfect a (hEF ha)) (fun a ha => (mem_filter.mp ha).2)
  have hlow : ∀ a ∈ E, ∀ p ∈ nonsingletonLabels (label a), (H : ℝ) ≤ p.val := by
    intro a ha p hp
    have hn : 0 < (labelOccurrences (label a) p).card :=
      lt_of_lt_of_le (by norm_num) (mem_filter.mp hp).2
    obtain ⟨t, ht⟩ := card_pos.mp hn
    have he : label a t = p := (mem_filter.mp ht).2
    rw [← he, hlabel a (hEF ha) t.1 t.2]
    exact_mod_cast hlo _ (hP t.2 (a.1 t.2 t.1).property)
  have hb := hdecay ↥(data.P ∪ data.Q) J R M Q D Y H Z P data.Q E forward j perfect cut
    (fun w q => origin (w, q)) Subtype.val (fun p => (data.prime p).pos)
    (fun p => hZ _ p.property) label
    (fun a => tupleForcedTarget data hZ (columnTupleWord a.1 forward a.2) (label a))
    base U weight (fun a => attachedCatalogAvoidance data s Z N (columnTupleWord a.1 forward a.2))
    cap W hR hRL hJ hM hT hRp hmass hQmass hV hprime hdisjoint
    (fun p hp => hlo p (hP j hp)) (fun p hp => hY p (hP j hp)) hQ hD hYexp hH
    (fun a ha => hq a (hEF ha)) (fun a ha => hd a (hEF ha))
    (fun a ha i => data.padding_squarefree _ (hpairs a (hEF ha) i))
    (fun a ha i => data.padding_pool _ (hpairs a (hEF ha) i))
    (fun a ha i => data.padding_card _ (hpairs a (hEF ha) i))
    (fun a ha => hrank a (hEF ha))
    (fun a ha i hi => horigin a ha i hi j) hW hWexp Subtype.val_injective
    (fun a ha => hU a (hEF ha)) hlow
    (fun a ha => supplied_tuple_padding_disjoint data a.1 a.2
      (hpairs a (hEF ha)) hprime hdisjoint)
    (fun a ha => supplied_tuple_label_seen data a.1 forward a.2 (hpairs a (hEF ha))
      hprime hdisjoint (label a) (hlabel a (hEF ha)))
    (fun a ha p hp => ⟨⟨p, data.supplied_word_support_subset _
      (columnTupleWord_pairs data a.1 forward a.2 (hpairs a (hEF ha))) hp⟩, rfl⟩)
    (fun a ha => hcap a (hEF ha)) (fun a ha => hw a (hEF ha))
    (fun a ha => hwcap a (hEF ha))
    (fun _ _ _ => witnessAvoidance_abs_le_one _ _)
    (fun a ha x hx => supplied_tuple_padding_retained data a.1 forward a.2
      (hpairs a (hEF ha)) hprime hdisjoint (label a) (hlabel a (hEF ha)) x
      (hpadding a (hEF ha) x hx))
    (fun a ha => hcost a (hEF ha))
  apply le_trans _ hb
  simp only [E, sum_filter, prohibitedDesignatedTerm, prohibitedWordDifference]
  rfl

end TwoPointCorrelations

end OAI
