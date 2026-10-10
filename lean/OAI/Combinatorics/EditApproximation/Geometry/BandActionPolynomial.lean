import OAI.Combinatorics.EditApproximation.Binary.BinaryBandAction
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

/-! A fixed-degree envelope for the full labeled action selector, including
its final logarithm-gradient and argmax, after the iterative optimizer. -/

namespace EditApproximation

private abbrev CE := FiniteBitPolynomial (Fin 12)
private def baSize (a : CE) : CE := .bitLength a
private def baMax (a b : CE) : CE := .maximum a b

private def expressionLogStorage (B K : CE) : CE :=
  baSize (2 * K) + 2 * (K * K * (4 * B + 18) + K * (baSize (2 * K + 1) + 1) + 1) + 1

private def expressionGradientStorage (G P L : CE) : CE :=
  4 * expressionLogStorage (2 * P + 2 * (5 + 50 * (baSize G + 2)) + 2) (G ^ 60) + 2 * L + 18

private def expressionPoint (K B Bv : CE) : CE :=
  Bv + 2 * (B + K * (2 * baSize (K + 1) + B)) + 2

private def expressionLogUniversal (B K : CE) : CE :=
  B + (baSize K + 2 * (K * K * B + K * (baSize (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * B + 1) + 2) + baSize (2 * K + 1) + 10

private def expressionLogStep (W K : CE) : CE :=
  (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) + 2100 * (W + 2) ^ 2 +
    6000 * (W + 1) ^ 2 + baSize (2 * K + 1) + 6

private def expressionLogBit (B K : CE) : CE :=
  let W := expressionLogUniversal (8 * B + 22) K
  12000 * (B + 4) ^ 2 + 2100 * (4 * B + 12) ^ 2 +
    K * expressionLogStep W K + 2000 * (W + 5) ^ 2 + 10

private def expressionGradientBit (G P L : CE) : CE :=
  let S := 3 + 50 * (baSize G + 2)
  let R := 4 * P + 2 * S + 8
  let logBits := expressionLogStorage R (G ^ 60)
  let natWidth := baMax (baSize G) 1
  let powerWidth := natWidth + 3 + 50 * (2 * natWidth + 1)
  (1 + 50 * (2000 * (powerWidth + 1) ^ 2 + 1)) + (4 * S + 3) +
    6000 * (P + S + 2) ^ 2 + expressionLogBit R (G ^ 60) +
    (6000 * (logBits + 4) ^ 2 + 1) + 6000 * (L + 2 * logBits + 9) ^ 2 + baSize G + 70

private def expressionMaximizer (d v B V : CE) : CE :=
  let W := B + baSize (d * V * V) + 2 * (1 + d * (B + B)) + 1
  v * (1 + d * (100000 * (W + 1) ^ 2) + 1000 * (W + 1) ^ 2 + 2) + d + 1

private def expressionUpdate (d K P : CE) : CE :=
  let C := baSize (K + 2) + 8
  let W := P + 2 * C + 8
  2100 * (baSize (K + 2) + 6) ^ 2 + (6000 * (C + 4) ^ 2 + 1) +
    d * (110000 * (W + 1) ^ 2 + 6) + baSize (K + 2) + 4

private def expressionOptimizer (d v G K B Bv L V : CE) : CE :=
  let P := expressionPoint K B Bv
  let W := expressionGradientStorage G (2 * P + 1) (2 * L + 1)
  d + 1 + K * (d * (expressionGradientBit G P L + 6) +
    expressionMaximizer d v (baMax P W) (2 * G ^ 60 + 1 + V + 1) + expressionUpdate d K P + 3)

private def expressionBandSumStorage (n B : CE) : CE :=
  baSize n + B + 2 * (1 + n * (B + 1)) + 2

private def expressionBandVertexWord (M B : CE) : CE :=
  2 * B + expressionBandSumStorage M B + 3

private def expressionStoredSumWord (n B : CE) : CE :=
  (B + 1) + baSize n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

private def expressionStoredSumBit (n B : CE) : CE :=
  1 + n * (100000 * (expressionStoredSumWord n B + 1) ^ 2)

private def expressionBandCoordinateBit (M B : CE) : CE :=
  2100 * (B + expressionBandSumStorage M B + 2) ^ 2

private def expressionBandPreparation (M d v B : CE) : CE :=
  expressionStoredSumBit M B + v * (d * (expressionBandCoordinateBit M B + 6)) + 6 * v

private def expressionOptimisticStorage (Bm Bt Bc : CE) : CE := 20 * Bt + 8 * Bm + 4 * Bc + 30

private def expressionOnlineStorage (Be Bk Bm Bt t : CE) : CE :=
  2 * Be + 2 * expressionBandSumStorage t (expressionOptimisticStorage Bm Bt (4 * Bk + 18)) +
    2 * (2 * Bt + 2 * Bm + 4) + 3

private def expressionGainBit (Bm Bt : CE) : CE := 2100 * (Bm + Bt + 2) ^ 2 + 1

private def expressionDecrementBit (Bm Bt : CE) : CE :=
  6000 * (Bt + 1) ^ 2 + 2100 * (8 * Bt + Bm + 8) ^ 2 + 2

private def expressionCoefficientBit (Bk : CE) : CE :=
  2000 * (Bk + 3) ^ 2 + 6000 * (2 * Bk + 7) ^ 2 + 2

private def expressionOptimisticBit (Bm Bt Bc : CE) : CE :=
  let W := 8 * Bt + 2 * Bm + 2 * Bc + 12
  expressionGainBit Bm Bt + expressionDecrementBit Bm Bt +
    2000 * (W + 1) ^ 2 + 6000 * (W + 1) ^ 2 + 2

private def expressionOnlineBit (Be Bk Bm Bt t : CE) : CE :=
  let storage := expressionOptimisticStorage Bm Bt (4 * Bk + 18)
  let W := Be + expressionBandSumStorage t storage + (2 * Bt + 2 * Bm + 4) + 2
  expressionCoefficientBit Bk + t * (expressionOptimisticBit Bm Bt (4 * Bk + 18) + 6) +
    expressionStoredSumBit t storage + expressionGainBit Bm Bt +
    6000 * (W + 1) ^ 2 + 2000 * (2 * W + 3) ^ 2 + 3

private def expressionSelection (d v G K B Bv L V : CE) : CE :=
  let P := expressionPoint K B Bv
  let W := expressionGradientStorage G (2 * P + 1) (2 * L + 1)
  expressionOptimizer d v G K B Bv L V + d * (expressionGradientBit G P L + 6) +
    expressionMaximizer d v (baMax P W) (2 * G ^ 60 + 1 + V + 1)

private def expressionEnvelopeWord (M bb B : CE) : CE := B + bb + baSize M + 8
private def expressionEnvelopeWork (M bb v B : CE) : CE :=
  let W := expressionEnvelopeWord M bb B
  2100 * (bb + baSize M + 6) ^ 2 +
    (1 + v * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + v + 4

private def bandActionExpression : CE :=
  let M := .input 0
  let d := .input 1
  let bb := .input 2
  let v := .input 3
  let G := .input 4
  let K := .input 5
  let t := .input 6
  let Be := .input 7
  let Bk := .input 8
  let Bi := .input 9
  let Bt := .input 10
  let E := .input 11
  let Bm := 3 * expressionEnvelopeWord M bb Bi + 1
  M * (expressionEnvelopeWork M bb v Bi + 6) +
    (expressionBandPreparation M d v Bm + 2 * v +
      d * (expressionOnlineBit Be Bk Bm Bt t + 6) +
      expressionSelection d v G K (expressionBandVertexWord M Bm) (expressionBandVertexWord M Bm)
        (expressionOnlineStorage Be Bk Bm Bt t) (E * (2 * t + 1)) + 2) + 1

def bandActionBitDegree : ℕ := bandActionExpression.degree

private def bandActionEnvironment (M d b v G K t Be Bk Bi Bt E : ℕ) : Fin 12 → ℕ
  | 0 => M
  | 1 => d
  | 2 => Nat.size b
  | 3 => v
  | 4 => G
  | 5 => K
  | 6 => t
  | 7 => Be
  | 8 => Bk
  | 9 => Bi
  | 10 => Bt
  | _ => E

private theorem bandActionExpression_eval (M d b v G K t Be Bk Bi Bt E : ℕ) :
    bandActionExpression.eval (bandActionEnvironment M d b v G K t Be Bk Bi Bt E) =
      BinaryFraction.bandActionBitBudget M d b v G K t Be Bk Bi Bt E := by
  have hnat : (BinaryFraction.nat G).width = max (Nat.size G) 1 := by
    simp only [BinaryFraction.nat, BinaryFraction.width, SignedBinary.ofInt,
      Int.natAbs_natCast, ← Nat.size_eq_bits_len, List.length_cons, List.length_nil]
  simp only [bandActionExpression, bandActionEnvironment, expressionSelection,
    expressionEnvelopeWord, expressionEnvelopeWork, expressionBandPreparation,
    expressionBandCoordinateBit, expressionBandVertexWord, expressionBandSumStorage,
    expressionStoredSumBit, expressionStoredSumWord, expressionOnlineBit,
    expressionOnlineStorage, expressionOptimisticStorage, expressionOptimisticBit,
    expressionGainBit, expressionDecrementBit, expressionCoefficientBit,
    expressionOptimizer, expressionPoint, expressionGradientStorage,
    expressionGradientBit, expressionLogStorage, expressionLogBit, expressionLogUniversal,
    expressionLogStep, expressionMaximizer, expressionUpdate, baSize, baMax,
    FiniteBitPolynomial.eval, BinaryFraction.bandActionBitBudget,
    BinaryFraction.preparedBandActionBitBudget, BinaryFraction.selectionBitBudget,
    BinaryFraction.bandEnvelopeWordBudget, BinaryFraction.bandEnvelopeBitBudget,
    BinaryFraction.bandPreparationBitBudget, BinaryFraction.bandCoordinateBitBudget,
    BinaryFraction.bandVertexWordBudget, BinaryFraction.bandMassTotalStorageBudget,
    BinaryFraction.storedSumBitBudget, BinaryFraction.storedSumWordBudget,
    BinaryFraction.onlineLinearBitBudget, BinaryFraction.onlineLinearStorageBudget,
    BinaryFraction.onlineFinalWordBudget, BinaryFraction.optimisticTermStorageBudget,
    BinaryFraction.optimisticTermBitBudget, BinaryFraction.optimisticTermWordBudget,
    BinaryFraction.gainBitBudget, BinaryFraction.decrementBitBudget,
    BinaryFraction.coefficientBitBudget, BinaryFraction.optimizerBitBudget,
    BinaryFraction.optimizerRoundBitBudget, BinaryFraction.optimizerPointWordBudget,
    BinaryFraction.optimizerGradientWordBudget, UnreducedRational.gradientStorageBudget,
    UnreducedRational.logarithmStorageBudget, BinaryFraction.gradientCellBitBudget,
    BinaryFraction.generalPowerWordBudget, BinaryFraction.smoothingStorageBudget,
    BinaryFraction.shiftedStorageBudget, BinaryFraction.gradientLogStorageBudget,
    BinaryFraction.logarithmBitBudget, BinaryFraction.logarithmUniversalWordBudget,
    BinaryFraction.logarithmPartialBitStep, BinaryFraction.maximizerBitBudget,
    BinaryFraction.maximizerWordBudget, BinaryFraction.dotWordBudget,
    BinaryFraction.optimizerUpdateBitBudget, BinaryFraction.updateCoordinateWordBudget,
    BinaryFraction.updateCoefficientWordBudget, hnat]
  rfl

theorem bandActionBitBudget_fixedPower (M d b v G K t Be Bk Bi Bt E S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hd : d ≤ S) (hb : Nat.size b ≤ S)
    (hv : v ≤ S) (hG : G ≤ S) (hK : K ≤ S) (ht : t ≤ S)
    (hBe : Be ≤ S) (hBk : Bk ≤ S) (hBi : Bi ≤ S) (hBt : Bt ≤ S) (hE : E ≤ S) :
    BinaryFraction.bandActionBitBudget M d b v G K t Be Bk Bi Bt E ≤ S ^ bandActionBitDegree := by
  have henv : ∀ i, bandActionEnvironment M d b v G K t Be Bk Bi Bt E i ≤ S := by
    intro i
    fin_cases i <;> simp only [bandActionEnvironment] <;> assumption
  simpa only [bandActionExpression_eval, bandActionBitDegree] using
    bandActionExpression.eval_le_pow _ S hS henv

end EditApproximation

end OAI
