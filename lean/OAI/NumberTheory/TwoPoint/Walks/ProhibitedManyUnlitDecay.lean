import OAI.NumberTheory.TwoPoint.Walks.ManyUnlitWeightedWords
import OAI.NumberTheory.TwoPoint.Bounds.NumericalTupleLabels
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms

namespace OAI

/-! The many-unlit bound for the original deleted-vertex trace terms. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_many_unlit_decay (C Ce Cs : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop, ∀ (R J M S B h s D : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (F : Finset (Fin R → SignedStep))
      (label : (Fin R → SignedStep) → Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (Fin R → SignedStep) → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (Fin R → SignedStep) → ℝ) (external H : ℝ),
      1 ≤ R → (R : ℝ) ≤ 2 * L →
      ((S + R * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((R * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ p ∈ data.P, H ≤ p) →
      (∀ w ∈ F, ∀ i, ((w i).tuple, (w i).padding) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i, (w i).tuple.primeFactors = univ.image (fun j => (label w (i, j)).val)) →
      (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) →
      (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B (List.ofFn w) x) →
      (∀ w ∈ F, cap w * 2 ^ (singletonLabels (label w)).card ≤
        crudeTraceWeight R S (fun i => (w i).padding) L external) →
      (∑ a ∈ largeUnlitCatalog F label L,
        prohibitedDesignatedTerm data hB s D (List.ofFn a.1) (label a.1) base (weight a.1) a.2) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_many_unlit_weighted_words C Ce Cs hC hCe hCs] with L hdecay
  intro R J M S B h s D data hB F label base weight cap external H
    hR hRL hS hJM hT hRp hexternal hext hP hQ hM hH hlo hpairs hlabel hcap hw hwcap hpadding hcost
  have hslots : ((R * (J + M) : ℕ) : ℝ) ≤ C * R * Real.log L := by
    have ht := mul_le_mul_of_nonneg_left hJM (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    push_cast at ht ⊢
    nlinarith
  have hlow : ∀ w ∈ F, ∀ p ∈ nonsingletonLabels (label w), H ≤ p.val := by
    intro w hw p hp
    have hn : 0 < (labelOccurrences (label w) p).card :=
      lt_of_lt_of_le (by norm_num) (mem_filter.mp hp).2
    obtain ⟨t, ht⟩ := card_pos.mp hn
    have hp' : p ∈ univ.image (label w) := mem_image.mpr ⟨t, mem_univ _, (mem_filter.mp ht).2⟩
    exact hlo p.val (numerical_label_pool data w (label w) (hpairs w hw) (hlabel w hw) p hp')
  have hb := hdecay ↥(data.P ∪ data.Q) R J (R * (J + M)) S B h data.P data.Q F label
    Subtype.val (fun p => (data.prime p).pos) (fun p => hB _ p.property)
    (fun w => tupleForcedTarget data hB (List.ofFn w) (label w)) base weight
    (fun w => attachedCatalogAvoidance data s B D (List.ofFn w)) cap external H
    hR hRL hS hexternal hext hslots hT hRp hP hQ
    (fun w hw => actualPrimeSlot_card_le w J M
      (fun i => (data.tuple_card _ (hpairs w hw i)).le)
      (fun i => data.padding_card _ (hpairs w hw i)))
    (fun w hw i => data.tuple_squarefree _ (hpairs w hw i))
    (fun w hw i => data.padding_squarefree _ (hpairs w hw i))
    (fun w hw i => data.tuple_pool _ (hpairs w hw i))
    (fun w hw i => data.padding_pool _ (hpairs w hw i))
    (fun w hw i j => data.disjoint.mono (data.tuple_pool _ (hpairs w hw i))
      (data.padding_pool _ (hpairs w hw j)))
    (fun w hw i => (show ((w i).padding.primeFactors.card : ℝ) ≤ M by
      exact_mod_cast data.padding_card _ (hpairs w hw i)).trans hM)
    hH Subtype.val_injective hlow
    (fun w hw => numerical_label_seen data w (label w) (hpairs w hw) (hlabel w hw))
    (fun w hw p hp => ⟨⟨p, data.supplied_word_support_subset _
      (numerical_word_pairs data w (hpairs w hw)) hp⟩, rfl⟩)
    hcap hw hwcap (fun _ _ _ => witnessAvoidance_abs_le_one _ _)
    (fun w hw x hx => numerical_padding_retained data w (label w) (hpairs w hw)
      (hlabel w hw) x (hpadding w hw x hx)) hcost
  exact hb

end TwoPointCorrelations

end OAI
