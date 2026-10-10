import OAI.NumberTheory.TwoPoint.Walks.HighRankTraceSlices
import OAI.NumberTheory.TwoPoint.Walks.RankSliceCost

namespace OAI

/-! The high-rank contribution with all designations, perfect-row sets and
columns summed.  Lit consistency supplies the arithmetic origin in each slice. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_high_rank_total (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Q D Y H B s N : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (cut : Fin R)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, P l ⊆ data.P) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) → (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ l, ∀ p ∈ P l, p.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, a.2 i) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        MainPaddingTests Subtype.val h B (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
          (by change 0 < R; omega) h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
        prohibitedDesignatedTerm data hB s N (columnTupleWord a.1 forward a.2)
          (label a) base (weight a) U) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_prohibited_high_rank_decay h Cj Cm Cw hCj hCm hCw,
    eventually_rank_slice_decay Cj hCj] with L hdecay hslice
  intro J R M Q D Y H B s N data hB P F forward cut label base weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
    hpairs hq hd hlabel hW hWexp hcap hw hwcap hpadding hcost
  refine le_trans ?_ (hslice R J hRL hJ)
  apply prohibited_high_rank_sum_le_uniform_slices data hB s N _ F label forward (by omega)
    cut base weight hw
  intro U perfect j
  let E := highRankTraceSlice F label forward (show 0 < R by omega) h
    ⌊L ^ (1 / 50 : ℝ)⌋₊ cut U perfect j
  have hEF : E ⊆ F := filter_subset _ _
  exact hdecay J R M Q D Y H B s N data hB P E forward j perfect cut label base U weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass (hV j) hprime hdisjoint hlo hY hQ hD hYexp hH
    (fun a ha => hpairs a (hEF ha)) (fun a ha => hq a (hEF ha))
    (fun a ha i => hd a (hEF ha) i j)
    (fun _ ha => (mem_filter.mp ha).2.2.2)
    (fun a ha => hlabel a (hEF ha))
    (fun _ ha => by rw [(mem_filter.mp ha).2.2.1]) hW hWexp
    (fun _ ha => (mem_filter.mp ha).2.1)
    (fun a ha => hcap a (hEF ha)) (fun a ha => hw a (hEF ha))
    (fun a ha => hwcap a (hEF ha)) (fun a ha => hpadding a (hEF ha))
    (fun a ha => hcost a (hEF ha))

end TwoPointCorrelations

end OAI
