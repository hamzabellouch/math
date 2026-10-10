import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Coarse.CoarsePrecision
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Construct the common denominator by Boolean products and binary
exponentiation, charging all intermediate bit operations. -/


 theorem coarseDenominatorWithWork_value (allowanceDen q L branching : List Bool) (D : ℕ) :
    bitWordValue (coarseDenominatorWithWork allowanceDen q L branching D).1 =
      coarseCommonDenominator (bitWordValue allowanceDen) (bitWordValue q)
        (bitWordValue L) (bitWordValue branching) D := by
  simp only [coarseDenominatorWithWork, trimBitWordWithWork_value,
    bitMulWithWork_value, bitPowerWithWork_value, coarseCommonDenominator]

 theorem coarseDenominatorWithWork_length (allowanceDen q L branching : List Bool) (D : ℕ) :
    (coarseDenominatorWithWork allowanceDen q L branching D).1.length =
      Nat.size (coarseCommonDenominator (bitWordValue allowanceDen) (bitWordValue q)
        (bitWordValue L) (bitWordValue branching) D) := by
  simp only [coarseDenominatorWithWork, trimBitWordWithWork_length,
    bitMulWithWork_value, bitPowerWithWork_value, trimBitWordWithWork_value,
    coarseCommonDenominator]

 theorem coarseDenominatorWithWork_cost (allowanceDen q L branching : List Bool) (D A : ℕ)
    (ha : allowanceDen.length ≤ A) (hq : q.length ≤ A) (hL : L.length ≤ A)
    (hb : branching.length ≤ A) :
    (coarseDenominatorWithWork allowanceDen q L branching D).2 ≤
      bitPowerBitBudget D (7 * A + 3) + 1000 * (10 * (D + 2) * (A + 1) + 1) ^ 2 := by
  let first := bitMulWithWork L branching
  let base := bitMulWithWork first.1 q
  let trimmed := trimBitWordWithWork base.1
  let power := bitPowerWithWork trimmed.1 D
  let initial := bitMulWithWork allowanceDen q
  let product := bitMulWithWork initial.1 power.1
  let W := 10 * (D + 2) * (A + 1)
  have hf := bitMulWithWork_cost L branching
  have hfl := bitMulWithWork_length L branching
  have hbc := bitMulWithWork_cost first.1 q
  have hbl := bitMulWithWork_length first.1 q
  have ht := (trimBitWordWithWork_cost base.1).le
  have htl : trimmed.1.length ≤ 7 * A + 3 := by
    have hh : trimmed.1.length ≤ base.1.length := by
      rw [trimBitWordWithWork_length]
      exact Nat.size_le.mpr (bitWordValue_lt_pow_length _)
    change base.1.length ≤ 2 * first.1.length + q.length + 1 at hbl
    change first.1.length ≤ 2 * L.length + branching.length + 1 at hfl
    omega
  have hp := bitPowerWithWork_cost trimmed.1 D (7 * A + 3) htl
  have hpl := bitPowerWithWork_length_le trimmed.1 D (7 * A + 3) htl
  have hi := bitMulWithWork_cost allowanceDen q
  have hil := bitMulWithWork_length allowanceDen q
  have hprod := bitMulWithWork_cost initial.1 power.1
  have hprodl := bitMulWithWork_length initial.1 power.1
  have htrim := trimBitWordWithWork_cost product.1
  have hfirst : first.1.length ≤ W := by
    change first.1.length ≤ 2 * L.length + branching.length + 1 at hfl
    dsimp only [W]
    nlinarith only [hfl, hL, hb, Nat.zero_le D, Nat.zero_le A]
  have hbase : base.1.length ≤ W := by
    change base.1.length ≤ 2 * first.1.length + q.length + 1 at hbl
    change first.1.length ≤ 2 * L.length + branching.length + 1 at hfl
    dsimp only [W]
    nlinarith only [hbl, hfl, hq, hL, hb, Nat.zero_le D, Nat.zero_le A]
  have hinitial : initial.1.length ≤ W := by
    change initial.1.length ≤ 2 * allowanceDen.length + q.length + 1 at hil
    dsimp only [W]
    nlinarith only [hil, ha, hq, Nat.zero_le D, Nat.zero_le A]
  have hpower : power.1.length ≤ W := by
    dsimp only [W]
    nlinarith only [hpl, Nat.zero_le D, Nat.zero_le A]
  have hAW : A ≤ W := by dsimp only [W]; nlinarith only [Nat.zero_le D, Nat.zero_le A]
  have bound (x y : List Bool) (hx : x.length ≤ W) (hy : y.length ≤ W) :
      (bitMulWithWork x y).2 ≤ 40 * (W + 1) ^ 2 := by
    apply (bitMulWithWork_cost x y).trans
    have hm := Nat.mul_le_mul (show x.length + 1 ≤ W + 1 by omega)
      (show x.length + y.length + 1 ≤ 2 * (W + 1) by omega)
    nlinarith only [hm]
  have hf' := bound L branching (hL.trans hAW) (hb.trans hAW)
  have hb' := bound first.1 q hfirst (hq.trans hAW)
  have hi' := bound allowanceDen q (ha.trans hAW) (hq.trans hAW)
  have hprod' := bound initial.1 power.1 hinitial hpower
  change base.1.length ≤ 2 * first.1.length + q.length + 1 at hbl
  change product.1.length ≤ 2 * initial.1.length + power.1.length + 1 at hprodl
  change first.2 + base.2 + trimmed.2 + power.2 + initial.2 + product.2 +
    (trimBitWordWithWork product.1).2 + 7 ≤ _
  change trimmed.2 ≤ 3 * base.1.length + 1 at ht
  change first.2 ≤ _ at hf'
  change base.2 ≤ _ at hb'
  change initial.2 ≤ _ at hi'
  change product.2 ≤ _ at hprod'
  change power.2 ≤ _ at hp
  change _ ≤ bitPowerBitBudget D (7 * A + 3) + 1000 * (W + 1) ^ 2
  nlinarith only [hf', hb', hi', hprod', hp, ht, htrim, hbase, hprodl, hinitial,
    hpower, Nat.zero_le W]

end EditApproximation

end OAI
