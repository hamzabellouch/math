import OAI.Combinatorics.EditApproximation.Coarse.CoarseCompactCells

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseGridNatWithWork_bounds (two : BinaryFraction) (den : List Bool)
    (hden : 0 < bitWordValue den) (n V D A : ℕ)
    (hd : bitWordValue den = two.representation.den) (hdl : den.length ≤ D)
    (hn : n ≤ V) (hb : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseGridNatWithWork den hden n).1 V D A := by
  have hv := coarseGridNatWithWork_value den hden n
  have hrd := (coarseGridNatWithWork_den den hden n).trans hd
  have hdl' : (coarseGridNatWithWork den hden n).1.denominator.length ≤ D := by
    change (trimBitWordWithWork den).1.length ≤ D
    rw [trimBitWordWithWork_length]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length den)).trans hdl
  refine ⟨hrd, hdl', ?_, ?_, ?_⟩
  · rw [hv]; positivity
  · rw [hv]; exact_mod_cast hn
  · apply (coarseCompact_width _ V D (coarseCompact_gridNat den hden n) ?_ ?_).trans hb
    · rw [hv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ n)]; exact_mod_cast hn
    · rw [coarseGridNatWithWork_den]
      exact (Nat.size_le.mpr (bitWordValue_lt_pow_length den)).trans hdl

 theorem coarseGridAddWithWork_bounds (two a b : BinaryFraction) (V W D A : ℕ)
    (ha : CoarseGridCell two a V D A) (hb : CoarseGridCell two b W D A)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseGridAddWithWork a b).1 (V + W) D A := by
  have hd : a.representation.den = b.representation.den := ha.1.trans hb.1.symm
  have hv := coarseGridAddWithWork_value a b hd
  have hnonneg : 0 ≤ a.value + b.value := add_nonneg ha.2.2.1 hb.2.2.1
  have hvalue : a.value + b.value ≤ ((V + W : ℕ) : ℚ) := by
    push_cast; exact add_le_add ha.2.2.2.1 hb.2.2.2.1
  refine ⟨(coarseGridAddWithWork_den a b).trans ha.1, ?_, ?_, ?_, ?_⟩
  · change (trimBitWordWithWork a.denominator).1.length ≤ D
    rw [trimBitWordWithWork_length]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length a.denominator)).trans ha.2.1
  · rw [hv]; exact hnonneg
  · rw [hv]; exact hvalue
  · exact (coarseGridAddWithWork_width a b (V + W) D hd
      (by rw [abs_of_nonneg hnonneg]; exact hvalue) ha.2.1).trans hbound

 theorem coarseGridCell_mono (two a : BinaryFraction) (V W D A : ℕ)
    (h : CoarseGridCell two a V D A) (hle : V ≤ W) : CoarseGridCell two a W D A := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans (by exact_mod_cast hle), h.2.2.2.2⟩

 theorem coarseGridZipMinimum_property (P : BinaryFraction → Prop)
    (left right : List BinaryFraction) (hl : ∀ a ∈ left, P a) (hr : ∀ a ∈ right, P a) :
    ∀ a ∈ (coarseGridZipMinimumWithWork left right).1, P a := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipMinimumWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipMinimumWithWork, List.not_mem_nil, false_implies, implies_true]
    | cons b right =>
      intro z hz
      change z ∈ (minWithWork a b).1 :: _ at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · unfold minWithWork
        dsimp only
        split_ifs
        · exact hl a List.mem_cons_self
        · exact hr b List.mem_cons_self
      · exact ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
          (fun b hb => hr b (List.mem_cons_of_mem _ hb)) z hz

 theorem coarseGridPenaltyWithWork_bounds (two : BinaryFraction) (source : List BinaryFraction)
    (V D A : ℕ) (htwo : two.value = 2) (htw : two.width ≤ A)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ A)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D A) :
    ∀ a ∈ (coarseGridPenaltyWithWork two source).1, CoarseGridCell two a V D A := by
  have hl := (coarseGridLeftWithWork_bounds two source V D A htwo htw hbound hs).1
  have hr := (coarseGridLeftWithWork_bounds two source.reverse V D A htwo htw hbound
    (fun a ha => hs a (List.mem_reverse.mp ha))).1
  exact coarseGridZipMinimum_property _ _ _ hl
    (fun a ha => hr a (List.mem_reverse.mp ha))

 theorem coarseContributionWithWork_bounds (two threshold scale a : BinaryFraction) (V W D A : ℕ)
    (ha : CoarseGridCell two a V D A) (hs : CoarseGridCell two scale W D A)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseContributionWithWork threshold scale a).1 (V + W) D A := by
  unfold coarseContributionWithWork
  dsimp only
  split_ifs
  · unfold maxWithWork
    dsimp only
    split_ifs
    · exact coarseGridCell_mono two scale W (V + W) D A hs (by omega)
    · exact coarseGridCell_mono two a V (V + W) D A ha (by omega)
  · exact coarseGridNatWithWork_bounds two a.denominator a.denominator_pos 0 (V + W) D A
      ha.1 ha.2.1 (by omega) hbound

end BinaryFraction
end EditApproximation

end OAI
