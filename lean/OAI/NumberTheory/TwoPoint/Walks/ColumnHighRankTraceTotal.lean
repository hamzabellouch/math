import OAI.NumberTheory.TwoPoint.Walks.HighRankTraceTotal
import OAI.NumberTheory.TwoPoint.Bounds.TraceCatalogMaps

namespace OAI

/-! The high-rank bound on the same column/padding catalog as the good class. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_column_high_rank_total (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Qmax D Y H B s N : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (forward : Fin R → Bool) (cut : Fin R)
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, P l ⊆ data.P) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) → (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ l, ∀ p ∈ P l, p.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      (Qmax : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, (a.2 i).val ≤ Qmax) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        MainPaddingTests Subtype.val h B (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward (fun i => (a.2 i).val) j)
          (by change 0 < R; omega) h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
        prohibitedDesignatedTerm data hB s N (columnTupleWord a.1 forward (fun i => (a.2 i).val))
          (label a) base (weight a) U) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_prohibited_high_rank_total h Cj Cm Cw hCj hCm hCw] with L hdecay
  intro J R M Qmax D Y H B s N data hB P Q F forward cut label base weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
    hpairs hq hd hlabel hW hWexp hcap hweight hwcap hpadding hcost
  by_cases hF : F.Nonempty
  · have : Nonempty (ColumnPrimeAssignment J R P × (Fin R → Q)) := ⟨hF.choose⟩
    let encode := columnNatCode (P := P) (Q := Q) (R := R)
    have hinj : Function.Injective encode := columnNatCode_injective
    let decode := Function.invFun encode
    have hdecode (a : ColumnPrimeAssignment J R P × (Fin R → Q)) : decode (encode a) = a :=
      Function.leftInverse_invFun hinj a
    let E := F.image encode
    have hpull (a : ColumnPrimeAssignment J R P × (Fin R → ℕ)) (ha : a ∈ E) :
        ∃ b ∈ F, a = encode b := by
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact ⟨b, hb, rfl⟩
    have hb := hdecay J R M Qmax D Y H B s N data hB P E forward cut
      (fun a => label (decode a)) base (fun a => weight (decode a)) (fun a => cap (decode a)) W
      hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; exact hpairs b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; exact hq b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; exact hd b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hlabel b hb)
      hW hWexp
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hcap b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hweight b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hwcap b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hpadding b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hcost b hb)
    rw [show E = F.image encode from rfl, sum_image (fun _ _ _ _ he => hinj he)] at hb
    simp only [hdecode] at hb
    simp only [encode, columnNatCode] at hb
    convert hb using 1
    apply sum_congr rfl
    intro a _
    apply sum_congr
    · ext U
      constructor
      · intro hU
        exact mem_filter.mpr (mem_filter.mp hU)
      · intro hU
        exact mem_filter.mpr (mem_filter.mp hU)
    · intro U _
      rfl
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI
