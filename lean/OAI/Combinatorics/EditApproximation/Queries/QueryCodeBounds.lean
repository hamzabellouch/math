import OAI.Combinatorics.EditApproximation.Queries.QueryOrderBounds

namespace OAI

/-! Key encoding uses only a fixed number of natural-word operations.
Its word sizes and Boolean work are polynomial in the coordinate widths. -/

namespace EditApproximation

theorem queryNaturalAdd_size (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  have h := bitAddWithWork_length a.bits b.bits false
  have hs := Nat.size_le.mpr (bitWordValue_lt_pow_length (binaryNaturalAddWithWork a b).1)
  rw [binaryNaturalAddWithWork_value] at hs
  simp only [binaryNaturalAddWithWork] at hs
  simp only [Nat.size_eq_bits_len] at h
  omega

theorem queryNaturalMul_size (a b : ℕ) : Nat.size (a * b) ≤ 2 * Nat.size a + Nat.size b + 1 := by
  have h := bitMulWithWork_length a.bits b.bits
  have hs := Nat.size_le.mpr (bitWordValue_lt_pow_length (binaryNaturalMulWithWork a b).1)
  rw [binaryNaturalMulWithWork_value] at hs
  simp only [binaryNaturalMulWithWork] at hs
  simp only [Nat.size_eq_bits_len] at h
  omega

theorem queryNaturalAdd_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalAddWithWork a b).2 ≤ 18 * K + 1 := by
  have h := binaryNaturalAddWithWork_cost a b
  omega

theorem queryNaturalMul_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (K + 1) * (2 * K + 1) := by
  apply (binaryNaturalMulWithWork_cost a b).trans
  gcongr
  omega

theorem queryChildCodeWithWork_bounds {M n : ℕ} (input : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    Nat.size (queryChildCodeWithWork input).1 ≤ 8 * (B + 1) ∧
      (queryChildCodeWithWork input).2 ≤ 100000 * (B + 1) ^ 2 := by
  have hi : Nat.size input.1.val ≤ B := (Nat.size_le_size input.1.isLt.le).trans hM
  have hl : Nat.size input.2.lo ≤ B :=
    (Nat.size_le_size (input.2.ordered.trans input.2.valid)).trans hn
  have hh : Nat.size input.2.hi ≤ B := (Nat.size_le_size input.2.valid).trans hn
  have hw : Nat.size (n + 1) ≤ B + 2 := by
    have h := queryNaturalAdd_size n 1
    norm_num only [Nat.size_one] at h
    omega
  have hhigh : Nat.size ((n + 1) * input.2.hi) ≤ 3 * B + 5 := by
    have h := queryNaturalMul_size (n + 1) input.2.hi
    omega
  have hcoord : Nat.size (input.2.lo + (n + 1) * input.2.hi) ≤ 4 * B + 6 := by
    have h := queryNaturalAdd_size input.2.lo ((n + 1) * input.2.hi)
    omega
  have hscaled : Nat.size (M * (input.2.lo + (n + 1) * input.2.hi)) ≤ 6 * B + 7 := by
    have h := queryNaturalMul_size M (input.2.lo + (n + 1) * input.2.hi)
    omega
  have hout : Nat.size (input.1.val + M * (input.2.lo + (n + 1) * input.2.hi)) ≤ 7 * B + 8 := by
    have h := queryNaturalAdd_size input.1.val (M * (input.2.lo + (n + 1) * input.2.hi))
    omega
  constructor
  · rw [queryChildCodeWithWork_value]
    exact hout.trans (by omega)
  · let K := 8 * (B + 1)
    have h1 : Nat.size 1 ≤ K := by norm_num only [Nat.size_one]; dsimp [K]; omega
    have hN : Nat.size n ≤ K := by dsimp [K]; omega
    have hW : Nat.size (n + 1) ≤ K := by dsimp [K]; omega
    have hI : Nat.size input.1.val ≤ K := by dsimp [K]; omega
    have hL : Nat.size input.2.lo ≤ K := by dsimp [K]; omega
    have hH : Nat.size input.2.hi ≤ K := by dsimp [K]; omega
    have hM' : Nat.size M ≤ K := by dsimp [K]; omega
    have hHigh : Nat.size ((n + 1) * input.2.hi) ≤ K := by dsimp [K]; omega
    have hCoord : Nat.size (input.2.lo + (n + 1) * input.2.hi) ≤ K := by dsimp [K]; omega
    have hScaled : Nat.size (M * (input.2.lo + (n + 1) * input.2.hi)) ≤ K := by dsimp [K]; omega
    have c1 := queryNaturalAdd_cost n 1 K hN h1
    have c2 := queryNaturalMul_cost (n + 1) input.2.hi K hW hH
    have c3 := queryNaturalAdd_cost input.2.lo ((n + 1) * input.2.hi) K hL hHigh
    have c4 := queryNaturalMul_cost M (input.2.lo + (n + 1) * input.2.hi) K hM' hCoord
    have c5 := queryNaturalAdd_cost input.1.val (M * (input.2.lo + (n + 1) * input.2.hi)) K hI hScaled
    simp only [queryChildCodeWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]
    dsimp only [K] at c1 c2 c3 c4 c5
    nlinarith only [c1, c2, c3, c4, c5, Nat.zero_le B]

theorem queryChildOrderWithWork_cost {M n : ℕ} (a b : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryEncodedLEWithWork queryChildCodeWithWork a b).2 ≤ 201000 * (B + 1) ^ 2 := by
  have ha := queryChildCodeWithWork_bounds a B hM hn
  have hb := queryChildCodeWithWork_bounds b B hM hn
  have h := queryEncodedLEWithWork_cost queryChildCodeWithWork a b
    (100000 * (B + 1) ^ 2) (8 * (B + 1)) ha.2 hb.2 ha.1 hb.1
  nlinarith only [h, Nat.zero_le B]

theorem queryOrderedChildInputsWithWork_cost {M n : ℕ} (inputs : List (Fin M × TargetInterval n))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryOrderedChildInputsWithWork inputs).2 ≤
      (inputs.length + 1) ^ 2 * (202000 * (B + 1) ^ 2) := by
  have h := queryOrderedInputsWithWork_cost childInputCode coordinateEqualWithWork
    (queryEncodedLEWithWork queryChildCodeWithWork)
    (fun a b => by simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value])
    (24 * B + 8) (201000 * (B + 1) ^ 2)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn)
    (fun a b => queryChildOrderWithWork_cost a b B hM hn) inputs
  apply h.trans
  gcongr
  nlinarith only [Nat.zero_le B]

end EditApproximation

end OAI
