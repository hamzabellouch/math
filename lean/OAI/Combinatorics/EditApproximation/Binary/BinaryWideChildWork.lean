import OAI.Combinatorics.EditApproximation.Binary.BinaryWideGridWork

namespace OAI

/-! Every child-grid list is constructed before the Cartesian product.
These bounds include the balanced endpoints, integer spacing and radius,
endpoint translations, and the two bounded grid loops. -/

namespace EditApproximation

theorem seedGridSpacingWithWork_bounds (b P B : ℕ)
    (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (seedGridSpacingWithWork b P).1.length ≤ B + 1 ∧
      (seedGridSpacingWithWork b P).2 ≤ 100 * (B + 2) ^ 2 := by
  let quotient := binaryNaturalDivModWithWork b P
  have hl := (bitDivModWithWork_lengths P.bits b.bits).1
  change quotient.1.length = b.bits.length at hl
  rw [Nat.size_eq_bits_len] at hl
  have hd := binaryNaturalDivModWithWork_cost b P
  have ht := wordLEWithWork_cost quotient.1 [true]
  change quotient.2.2 ≤ _ at hd
  simp only [List.length_cons, List.length_nil] at ht
  unfold seedGridSpacingWithWork
  dsimp only
  constructor
  · split_ifs
    · simp only [List.length_cons, List.length_nil]
      omega
    · change quotient.1.length ≤ B + 1
      omega
  · change quotient.2.2 + (wordLEWithWork quotient.1 [true]).2 + 2 ≤ _
    nlinarith only [hd, ht, hl, hb, hP, Nat.zero_le B]

theorem gridStateBoxBitBudget_mono_count (k l B : ℕ) (h : k ≤ l) :
    gridStateBoxBitBudget k B ≤ gridStateBoxBitBudget l B := by
  unfold gridStateBoxBitBudget gridPointsBitBudget
  gcongr

def wideChildGridBitBudget (P B : ℕ) : ℕ :=
  10000 * (B + 12) ^ 2 + gridStateBoxBitBudget (40 * P + 2) (B + 12)

theorem wideChildGridWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P B : ℕ) (i : Fin M) (hPpos : 0 < P)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (wideChildGridWithWork parent r b P i).2 ≤ wideChildGridBitBudget P B := by
  let child := sourceChildWithWork parent i
  let spacing := seedGridSpacingWithWork b P
  let radius := binaryNaturalMulWithWork 10 b
  let leftOffset := saturatingSubtractWithWork child.1.lo parent.lo
  let rightOffset := saturatingSubtractWithWork child.1.hi parent.lo
  let left := binaryNaturalAddWithWork r.lo (bitWordValue leftOffset.1)
  let right := binaryNaturalAddWithWork r.lo (bitWordValue rightOffset.1)
  have hparent : Nat.size parent.lo ≤ B :=
    (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
  have hcl : Nat.size child.1.lo ≤ B :=
    (Nat.size_le_size (child.1.ordered.trans child.1.valid)).trans hnx
  have hch : Nat.size child.1.hi ≤ B := (Nat.size_le_size child.1.valid).trans hnx
  have hrlo : Nat.size r.lo ≤ B := (Nat.size_le_size (r.ordered.trans r.valid)).trans hny
  have hlo : Nat.size (bitWordValue leftOffset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hcl
  have hro : Nat.size (bitWordValue rightOffset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hch
  have hleft : Nat.size (bitWordValue left.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hright : Nat.size (bitWordValue right.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hspacing := seedGridSpacingWithWork_bounds b P B hb hP
  have hspacingCost : spacing.2 ≤ 100 * (B + 2) ^ 2 := hspacing.2
  have hgs : Nat.size (bitWordValue spacing.1) ≤ B + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hspacing.1
  have hrl := bitMulWithWork_length (10 : ℕ).bits b.bits
  change radius.1.length ≤ _ at hrl
  simp only [Nat.size_eq_bits_len] at hrl
  have hten : Nat.size 10 = 4 := by decide
  rw [hten] at hrl
  have hrs : Nat.size (bitWordValue radius.1) ≤ B + 9 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans (by omega)
  have hg := seedGridSpacingWithWork_pos b P hPpos
  have hgrid := gridStateBoxWithWork_cost ny (bitWordValue spacing.1) (bitWordValue radius.1)
    (bitWordValue left.1) (bitWordValue right.1) (B + 12) hg
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcount : 2 * bitWordValue radius.1 / bitWordValue spacing.1 + 2 ≤ 40 * P + 2 := by
    rw [binaryNaturalMulWithWork_value, seedGridSpacingWithWork_value b P hPpos]
    simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hPpos
  have hgrid' := hgrid.trans (gridStateBoxBitBudget_mono_count _ _ (B + 12) hcount)
  have hc := sourceChildWithWork_cost parent i B hnx hM
  have hrad := binaryNaturalMulWithWork_cost 10 b
  have hol := saturatingSubtractWithWork_cost child.1.lo parent.lo
  have hor := saturatingSubtractWithWork_cost child.1.hi parent.lo
  have hal := binaryNaturalAddWithWork_cost r.lo (bitWordValue leftOffset.1)
  have har := binaryNaturalAddWithWork_cost r.lo (bitWordValue rightOffset.1)
  change child.2 ≤ _ at hc
  change radius.2 ≤ _ at hrad
  change leftOffset.2 ≤ _ at hol
  change rightOffset.2 ≤ _ at hor
  change left.2 ≤ _ at hal
  change right.2 ≤ _ at har
  rw [hten] at hrad
  change child.2 + spacing.2 + radius.2 + leftOffset.2 + rightOffset.2 + left.2 + right.2 + _ + 8 ≤ _
  unfold wideChildGridBitBudget
  nlinarith only [hc, hspacingCost, hrad, hol, hor, hal, har, hgrid', hcl, hch, hparent,
    hrlo, hlo, hro, hb, Nat.zero_le B]

end EditApproximation

end OAI
