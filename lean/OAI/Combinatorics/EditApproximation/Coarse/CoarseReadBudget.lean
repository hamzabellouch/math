import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadNumericalBounds

namespace OAI

namespace EditApproximation

/-- A finite uniform bound on the actually executed source-index operations.
The depth and offset ranges are the original padded source capacity. -/
structure CoarseReadBudget (B R k n : ℕ) (source target : List ℕ) (K : ℕ) : Prop where
  descriptor : ∀ d ≤ R, ∀ offset ≤ B ^ R, (coarseDescriptorWithWork B d n offset).2 ≤ K
  power : ∀ d ≤ R, (bitPowerWithWork B.bits d).2 ≤ K
  offset : ∀ offset ≤ B ^ R, ∀ i : Fin B,
    ∀ d ≤ R, (coarseChildOffsetWithWork offset (B ^ d) i.val).2 ≤ K
  advance : ∀ s ≤ n, ∀ width ≤ n, (binaryNaturalAddWithWork s width).2 ≤ K
  sourceRead : ∀ offset ≤ B ^ R, (coarsePaddedReadWithWork n source offset).2 ≤ K
  mismatch : ∀ offset ≤ B ^ R, ∀ s ≤ n, ∀ shift : Fin (2 * k + 1),
    (BinaryFraction.coarseReadShiftWithWork k n target
      (coarsePaddedRead n source offset) s shift).2 ≤ K

theorem coarseReadBudget_height (B R k n H : ℕ) (source target : List ℕ)
    (hH : 10 ≤ H) (hR : R ≤ H) (hBpos : 1 ≤ B)
    (hB : Nat.size B ≤ H ^ 3) (hcap : Nat.size (B ^ R) ≤ H ^ 3)
    (hn : Nat.size n ≤ H ^ 3) (hk : Nat.size (2 * k + 1) ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3) :
    CoarseReadBudget B R k n source target (H ^ 30) := by
  have hoff (offset : ℕ) (ho : offset ≤ B ^ R) : Nat.size offset ≤ H ^ 3 :=
    (Nat.size_le_size ho).trans hcap
  have hpow (d : ℕ) (hd : d ≤ R) : Nat.size (B ^ d) ≤ H ^ 3 :=
    (Nat.size_le_size (Nat.pow_le_pow_right hBpos hd)).trans hcap
  have hsmall : 20 * (H ^ 3 + 1) ≤ H ^ 30 := by
    have hu : 20 * (H ^ 3 + 1) ≤ BinaryFraction.coarseNumericalUnit H := by
      unfold BinaryFraction.coarseNumericalUnit
      nlinarith only [Nat.zero_le (bitPowerBitBudget H (7 * H ^ 3 + 3)),
        Nat.zero_le (1000 * (10 * (H + 2) * (H ^ 3 + 1) + 1) ^ 2),
        Nat.zero_le (H ^ 3)]
    exact hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd offset ho
    exact coarseDescriptorWithWork_height_bound B d n offset H hH (hd.trans hR) hB hn (hoff _ ho)
  · intro d hd
    have hc := bitPowerWithWork_cost B.bits d (H ^ 3) (by simpa only [← Nat.size_eq_bits_len] using hB)
    have hm := BinaryFraction.bitPowerBitBudget_mono d H (H ^ 3) (7 * H ^ 3 + 3)
      (hd.trans hR) (by omega)
    have hu : bitPowerBitBudget H (7 * H ^ 3 + 3) ≤ BinaryFraction.coarseNumericalUnit H := by
      unfold BinaryFraction.coarseNumericalUnit
      omega
    exact hc.trans (hm.trans (hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)))
  · intro offset ho i d hd
    exact coarseChildOffsetWithWork_height_bound offset (B ^ d) i.val H hH (hoff _ ho)
      (hpow _ hd) ((Nat.size_le_size (Nat.le_of_lt i.isLt)).trans hB)
  · intro s hs width hw
    have hc := binaryNaturalAddWithWork_cost s width
    have hb1 := (Nat.size_le_size hs).trans hn
    have hb2 := (Nat.size_le_size hw).trans hn
    omega
  · intro offset ho
    have hc := coarsePaddedReadWithWork_cost n source offset (H ^ 3) hn (hoff _ ho)
    omega
  · intro offset ho s hs shift
    exact coarseReadShiftWithWork_height_bound k n target (coarsePaddedRead n source offset)
      s shift H hH ((Nat.size_le_size (by omega : k ≤ 2 * k + 1)).trans hk) hn
      ((Nat.size_le_size hs).trans hn) ((Nat.size_le_size (Nat.le_of_lt shift.isLt)).trans hk)
      (fun a ha => hsymbol a (List.mem_append_right source ha))
      (fun a ha => hsymbol a (List.mem_append_left target (coarsePaddedRead_symbol_mem n source offset a ha)))

end EditApproximation

end OAI
