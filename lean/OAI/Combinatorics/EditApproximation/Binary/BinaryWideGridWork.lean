import OAI.Combinatorics.EditApproximation.Binary.BinaryWideGrid
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGridWork

namespace OAI

/-! Polynomial per-child bit work before the explicitly counted Cartesian
product. All interval endpoints and arities are bounded by their input
word sizes; no good-seed premise occurs in these bounds. -/

namespace EditApproximation

theorem balancedCutWithWork_cost (lo width M i B : ℕ) (hM : 0 < M)
    (hl : Nat.size lo ≤ B) (hw : Nat.size width ≤ B)
    (hm : Nat.size M ≤ B) (hi : Nat.size i ≤ B) :
    (balancedCutWithWork lo width M i).2 ≤ 1000 * (B + 1) ^ 2 := by
  let product := binaryNaturalMulWithWork i width
  let quotient := binaryNaturalDivModWithWork (bitWordValue product.1) M
  have hp := binaryNaturalMulWithWork_cost i width
  have hpl := bitMulWithWork_length i.bits width.bits
  have hps : Nat.size (bitWordValue product.1) ≤ 3 * B + 1 := by
    have hv : Nat.size (bitWordValue product.1) ≤ product.1.length :=
      Nat.size_le.mpr (bitWordValue_lt_pow_length _)
    change product.1.length ≤ _ at hpl
    simp only [Nat.size_eq_bits_len] at hpl
    omega
  have hq := binaryNaturalDivModWithWork_cost (bitWordValue product.1) M
  have hqs : Nat.size (bitWordValue quotient.1) ≤ 3 * B + 1 := by
    rw [(binaryNaturalDivModWithWork_spec _ M hM).1]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hps
  have ha := binaryNaturalAddWithWork_cost lo (bitWordValue quotient.1)
  change product.2 + quotient.2.2 + (binaryNaturalAddWithWork lo (bitWordValue quotient.1)).2 + 2 ≤ _
  nlinarith only [hp, hq, ha, hps, hqs, hl, hw, hm, hi, Nat.zero_le B]

theorem sourceChildWithWork_cost {n M : ℕ} (parent : TargetInterval n) (i : Fin M)
    (B : ℕ) (hn : Nat.size n ≤ B) (hm : Nat.size M ≤ B) :
    (sourceChildWithWork parent i).2 ≤ 2200 * (B + 3) ^ 2 := by
  have hlo := (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hn
  have hhi := (Nat.size_le_size parent.valid).trans hn
  have hi := (Nat.size_le_size i.isLt.le).trans hm
  let width := saturatingSubtractWithWork parent.hi parent.lo
  let next := binaryNaturalAddWithWork i.val 1
  have hwidth : Nat.size (bitWordValue width.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hhi
  have hnext : Nat.size (bitWordValue next.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    have h := binaryNaturalAdd_size_le i.val 1
    simp only [Nat.size_one] at h
    have hMpos : 1 ≤ Nat.size M := Nat.size_pos.mpr (Nat.zero_lt_of_lt i.isLt)
    omega
  have hleft := balancedCutWithWork_cost parent.lo (bitWordValue width.1) M i.val (B + 2)
    (Nat.zero_lt_of_lt i.isLt) (by omega) (by omega) (by omega) (by omega)
  have hright := balancedCutWithWork_cost parent.lo (bitWordValue width.1) M
    (bitWordValue next.1) (B + 2) (Nat.zero_lt_of_lt i.isLt)
    (by omega) (by omega) (by omega) hnext
  have hsub := saturatingSubtractWithWork_cost parent.hi parent.lo
  have hadd := binaryNaturalAddWithWork_cost i.val 1
  change width.2 + next.2 + _ + _ + 4 ≤ _
  change width.2 ≤ _ at hsub
  change next.2 ≤ _ at hadd
  simp only [Nat.size_one] at hadd
  nlinarith only [hleft, hright, hsub, hadd, hlo, hhi, hi, Nat.zero_le B]

end EditApproximation

end OAI
