import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetup
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGridWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The optimizer's sampled iteration is obtained by the exact triangular
block search, with every threshold multiplication and comparison charged. -/

namespace EditApproximation



@[simp] theorem triangularMassWithWork_value (K : ℕ) :
    bitWordValue (triangularMassWithWork K).1 = optimizerTriangularMass K := by
  simp only [triangularMassWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value,
    (binaryNaturalDivModWithWork_spec _ 2 (by decide)).1]
  rw [← optimizerTriangularMass_twice K, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]



@[simp] theorem triangularChoiceWithWork_value (K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    (triangularChoiceWithWork K integer).1 = triangularChoice K integer := by
  induction K with
  | zero => exact Fin.elim0 integer
  | succ K ih =>
    change (let threshold := triangularMassWithWork K
      let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
      if h : test.1 = .lt then
        let hsmall : integer.val < optimizerTriangularMass K := by
          have ht := (binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, triangularMassWithWork_value] using ht
        let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
        (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
      else (⟨K, Nat.lt_succ_self K⟩, threshold.2 + test.2 + 1) : Fin (K + 1) × ℕ).1 = _
    unfold triangularChoice
    dsimp only
    by_cases hs : integer.val < optimizerTriangularMass K
    · have ht : (binaryNaturalCompareWithWork integer.val
          (bitWordValue (triangularMassWithWork K).1)).1 = .lt := by
        apply (binaryNaturalCompareWithWork_lt _ _).mpr
        simpa only [triangularMassWithWork_value] using hs
      simp only [ht, dite_true, hs, ih]
    · have ht : (binaryNaturalCompareWithWork integer.val
          (bitWordValue (triangularMassWithWork K).1)).1 ≠ .lt := by
        intro ht
        apply hs
        simpa only [triangularMassWithWork_value] using (binaryNaturalCompareWithWork_lt _ _).mp ht
      simp only [ht, dite_false, hs]

theorem triangularMassWithWork_bounds (K B : ℕ) (hK : Nat.size K ≤ B) :
    (triangularMassWithWork K).1.length ≤ 3 * B + 4 ∧
      (triangularMassWithWork K).2 ≤ 10000 * (B + 3) ^ 2 := by
  let next := binaryNaturalAddWithWork K 1
  let product := binaryNaturalMulWithWork K (bitWordValue next.1)
  let quotient := binaryNaturalDivModWithWork (bitWordValue product.1) 2
  have hn : Nat.size (bitWordValue next.1) ≤ B + 3 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le K 1).trans (by simp only [Nat.size_one]; omega)
  have hp := bitMulWithWork_length K.bits (bitWordValue next.1).bits
  change product.1.length ≤ _ at hp
  simp only [Nat.size_eq_bits_len] at hp
  have hps : Nat.size (bitWordValue product.1) ≤ 3 * B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length product.1)).trans (by omega)
  have hq := (bitDivModWithWork_lengths (2 : ℕ).bits (bitWordValue product.1).bits).1
  change quotient.1.length = _ at hq
  rw [Nat.size_eq_bits_len] at hq
  have hc1 := binaryNaturalAddWithWork_cost K 1
  have hc2 := binaryNaturalMulWithWork_cost K (bitWordValue next.1)
  have hc3 := binaryNaturalDivModWithWork_cost (bitWordValue product.1) 2
  simp only [Nat.size_one, show Nat.size 2 = 2 by decide] at hc1 hc3
  constructor
  · change quotient.1.length ≤ _
    omega
  · change next.2 + product.2 + quotient.2.2 + 3 ≤ _
    change next.2 ≤ _ at hc1
    change product.2 ≤ _ at hc2
    change quotient.2.2 ≤ _ at hc3
    nlinarith only [hc1, hc2, hc3, hK, hn, hps, Nat.zero_le B]

def triangularChoiceBitBudget (K B : ℕ) : ℕ :=
  (K + 1) * (10000 * (B + 3) ^ 2 + 30 * (B + 3))

theorem triangularChoiceWithWork_cost (K : ℕ) (integer : Fin (optimizerTriangularMass K))
    (B : ℕ) (hK : Nat.size K ≤ B) (hi : Nat.size integer.val ≤ B) :
    (triangularChoiceWithWork K integer).2 ≤ triangularChoiceBitBudget K B := by
  induction K generalizing B with
  | zero => exact Fin.elim0 integer
  | succ K ih =>
    have hprev : Nat.size K ≤ B := (Nat.size_le_size (Nat.le_succ K)).trans hK
    have hthreshold := triangularMassWithWork_bounds K B hprev
    have hs : Nat.size (bitWordValue (triangularMassWithWork K).1) ≤ 3 * B + 4 :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hthreshold.1
    have hcompare := binaryNaturalCompareWithWork_cost integer.val
      (bitWordValue (triangularMassWithWork K).1)
    change (let threshold := triangularMassWithWork K
      let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
      if h : test.1 = .lt then
        let hsmall : integer.val < optimizerTriangularMass K := by
          have ht := (binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, triangularMassWithWork_value] using ht
        let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
        (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
      else (⟨K, Nat.lt_succ_self K⟩, threshold.2 + test.2 + 1) : Fin (K + 1) × ℕ).2 ≤ _
    dsimp only
    split_ifs with h
    · have hsmall : integer.val < optimizerTriangularMass K := by
        have hc := (binaryNaturalCompareWithWork_lt _ _).mp h
        simpa only [triangularMassWithWork_value] using hc
      have hr := ih ⟨integer.val, hsmall⟩ B hprev hi
      unfold triangularChoiceBitBudget at hr ⊢
      nlinarith only [hthreshold.2, hcompare, hr, hs, hi, Nat.zero_le K, Nat.zero_le B]
    · unfold triangularChoiceBitBudget
      nlinarith only [hthreshold.2, hcompare, hs, hi, Nat.zero_le K, Nat.zero_le B]

end EditApproximation

end OAI
