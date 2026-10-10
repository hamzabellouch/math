import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOptimizer

namespace OAI

/-! A fixed polynomial envelope for the executed Boolean optimizer.
The expression below records precisely the arithmetic cost formula; its
degree proof avoids expanding powers or changing any computational limit. -/

namespace EditApproximation

private inductive NumericalCostInput
  | dimension | vertices | parameter | iterations | denominator | vertexBits | linearBits | linearValue
  | branches | history | etaBits | kappaBits | massBits | tableBits | etaValue

private inductive NumericalCostExpression
  | input (i : NumericalCostInput)
  | constant (n : ℕ)
  | add (a b : NumericalCostExpression)
  | mul (a b : NumericalCostExpression)
  | pow (a : NumericalCostExpression) (n : ℕ)
  | maximum (a b : NumericalCostExpression)
  | bitLength (a : NumericalCostExpression)

private instance (n : ℕ) : OfNat NumericalCostExpression n := ⟨.constant n⟩
private instance : Add NumericalCostExpression := ⟨.add⟩
private instance : Mul NumericalCostExpression := ⟨.mul⟩
private instance : Pow NumericalCostExpression ℕ := ⟨.pow⟩

private def NumericalCostExpression.eval (env : NumericalCostInput → ℕ) : NumericalCostExpression → ℕ
  | .input i => env i
  | .constant n => n
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .pow a n => a.eval env ^ n
  | .maximum a b => max (a.eval env) (b.eval env)
  | .bitLength a => Nat.size (a.eval env)

private def NumericalCostExpression.degree : NumericalCostExpression → ℕ
  | .input _ => 1
  | .constant n => Nat.size n
  | .add a b => max a.degree b.degree + 1
  | .mul a b => a.degree + b.degree
  | .pow a n => a.degree * n
  | .maximum a b => max a.degree b.degree
  | .bitLength a => a.degree

private theorem NumericalCostExpression.eval_le_pow (a : NumericalCostExpression)
    (env : NumericalCostInput → ℕ) (S : ℕ) (hS : 2 ≤ S) (henv : ∀ i, env i ≤ S) :
    a.eval env ≤ S ^ a.degree := by
  induction a with
  | input i => simpa only [eval, degree, pow_one] using henv i
  | constant n =>
    exact (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_left hS _)
  | add a b ha hb =>
    have ha' := ha.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_left a.degree b.degree))
    have hb' := hb.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_right a.degree b.degree))
    change a.eval env + b.eval env ≤ S ^ (max a.degree b.degree + 1)
    calc
      _ ≤ 2 * S ^ max a.degree b.degree := by omega
      _ ≤ S * S ^ max a.degree b.degree := Nat.mul_le_mul_right _ hS
      _ = _ := (pow_succ' S _).symm
  | mul a b ha hb =>
    exact (Nat.mul_le_mul ha hb).trans_eq (pow_add S a.degree b.degree).symm
  | pow a n ha =>
    exact (Nat.pow_le_pow_left ha n).trans_eq (pow_mul S a.degree n).symm
  | maximum a b ha hb =>
    exact max_le
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
      (hb.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_right a.degree b.degree)))
  | bitLength a ha => exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans ha

private def numericalCostEnvironment (d v G K B Bv L V : ℕ) : NumericalCostInput → ℕ
  | .dimension => d
  | .vertices => v
  | .parameter => G
  | .iterations => K
  | .denominator => B
  | .vertexBits => Bv
  | .linearBits => L
  | .linearValue => V
  | _ => 0

private abbrev CE := NumericalCostExpression

private def costSize (a : CE) : CE := .bitLength a
private def costMax (a b : CE) : CE := .maximum a b

private def expressionLogStorage (B K : CE) : CE :=
  costSize (2 * K) + 2 * (K * K * (4 * B + 18) + K * (costSize (2 * K + 1) + 1) + 1) + 1

private def expressionGradientStorage (G P L : CE) : CE :=
  4 * expressionLogStorage (2 * P + 2 * (5 + 50 * (costSize G + 2)) + 2) (G ^ 60) + 2 * L + 18

private def expressionPoint (K B Bv : CE) : CE :=
  Bv + 2 * (B + K * (2 * costSize (K + 1) + B)) + 2

private def expressionLogUniversal (B K : CE) : CE :=
  B + (costSize K + 2 * (K * K * B + K * (costSize (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * B + 1) + 2) + costSize (2 * K + 1) + 10

private def expressionLogStep (W K : CE) : CE :=
  (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) + 2100 * (W + 2) ^ 2 +
    6000 * (W + 1) ^ 2 + costSize (2 * K + 1) + 6

private def expressionLogBit (B K : CE) : CE :=
  let W := expressionLogUniversal (8 * B + 22) K
  12000 * (B + 4) ^ 2 + 2100 * (4 * B + 12) ^ 2 +
    K * expressionLogStep W K + 2000 * (W + 5) ^ 2 + 10

private def expressionGradientBit (G P L : CE) : CE :=
  let S := 3 + 50 * (costSize G + 2)
  let R := 4 * P + 2 * S + 8
  let logBits := expressionLogStorage R (G ^ 60)
  let natWidth := costMax (costSize G) 1
  let powerWidth := natWidth + 3 + 50 * (2 * natWidth + 1)
  (1 + 50 * (2000 * (powerWidth + 1) ^ 2 + 1)) + (4 * S + 3) +
    6000 * (P + S + 2) ^ 2 + expressionLogBit R (G ^ 60) +
    (6000 * (logBits + 4) ^ 2 + 1) + 6000 * (L + 2 * logBits + 9) ^ 2 + costSize G + 70

private def expressionMaximizer (d v B V : CE) : CE :=
  let W := B + costSize (d * V * V) + 2 * (1 + d * (B + B)) + 1
  v * (1 + d * (100000 * (W + 1) ^ 2) + 1000 * (W + 1) ^ 2 + 2) + d + 1

private def expressionUpdate (d K P : CE) : CE :=
  let C := costSize (K + 2) + 8
  let W := P + 2 * C + 8
  2100 * (costSize (K + 2) + 6) ^ 2 + (6000 * (C + 4) ^ 2 + 1) +
    d * (110000 * (W + 1) ^ 2 + 6) + costSize (K + 2) + 4

private def expressionOptimizer (d v G K B Bv L V : CE) : CE :=
  let P := expressionPoint K B Bv
  let W := expressionGradientStorage G (2 * P + 1) (2 * L + 1)
  d + 1 + K * (d * (expressionGradientBit G P L + 6) +
    expressionMaximizer d v (costMax P W) (2 * G ^ 60 + 1 + V + 1) + expressionUpdate d K P + 3)


private def optimizerCostExpression : CE :=
  expressionOptimizer (.input .dimension) (.input .vertices) (.input .parameter) (.input .iterations)
    (.input .denominator) (.input .vertexBits) (.input .linearBits) (.input .linearValue)

def optimizerBitPolynomialDegree : ℕ := optimizerCostExpression.degree

private theorem optimizerCostExpression_eval (d v G K B Bv L V : ℕ) :
    optimizerCostExpression.eval (numericalCostEnvironment d v G K B Bv L V) =
      BinaryFraction.optimizerBitBudget d v G K B Bv L V := by
  have hnat : (BinaryFraction.nat G).width = max (Nat.size G) 1 := by
    simp only [BinaryFraction.nat, BinaryFraction.width, SignedBinary.ofInt,
      Int.natAbs_natCast, ← Nat.size_eq_bits_len, List.length_cons, List.length_nil]
  simp only [optimizerCostExpression, expressionOptimizer, expressionPoint, expressionGradientStorage,
    expressionGradientBit, expressionLogStorage, expressionLogBit, expressionLogUniversal,
    expressionLogStep, expressionMaximizer, expressionUpdate, costSize, costMax,
    NumericalCostExpression.eval, numericalCostEnvironment, BinaryFraction.optimizerBitBudget,
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

theorem optimizerBitBudget_le_fixed_power (d v G K B Bv L V S : ℕ) (hS : 2 ≤ S)
    (hd : d ≤ S) (hv : v ≤ S) (hG : G ≤ S) (hK : K ≤ S)
    (hB : B ≤ S) (hBv : Bv ≤ S) (hL : L ≤ S) (hV : V ≤ S) :
    BinaryFraction.optimizerBitBudget d v G K B Bv L V ≤ S ^ optimizerBitPolynomialDegree := by
  rw [← optimizerCostExpression_eval]
  apply NumericalCostExpression.eval_le_pow _ _ S hS
  intro i
  cases i <;> first | assumption | exact Nat.zero_le _

theorem booleanOptimizer_cost_le_fixed_power {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d)
    (G K B Bv L V S : ℕ) (hS : 2 ≤ S) (hd : d ≤ S) (hv : vertices.length ≤ S)
    (hG : G ≤ S) (hK : K ≤ S) (hB : B ≤ S) (hBv : Bv ≤ S) (hL : L ≤ S) (hV : V ≤ S)
    (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧ Nat.size (v.get i).representation.den ≤ B)
    (hvw : ∀ v ∈ vertices, ∀ i, (v.get i).width ≤ Bv)
    (hlw : ∀ i, (linear.get i).width ≤ L) (hlv : ∀ i, |(linear.get i).value| ≤ V) :
    (BinaryFraction.finiteOptimizerWithWork vertices linear G K).2 ≤ S ^ optimizerBitPolynomialDegree :=
  (BinaryFraction.finiteOptimizerWithWork_cost vertices linear G K B Bv L V hvertices hinput hvw hlw hlv).trans
    (optimizerBitBudget_le_fixed_power d vertices.length G K B Bv L V S hS hd hv hG hK hB hBv hL hV)


private def expressionBandSumStorage (n B : CE) : CE :=
  costSize n + B + 2 * (1 + n * (B + 1)) + 2

private def expressionBandVertexWord (M B : CE) : CE :=
  2 * B + expressionBandSumStorage M B + 3

private def expressionStoredSumWord (n B : CE) : CE :=
  (B + 1) + costSize n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

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

private def preparedOptimizerCostExpression : CE :=
  let M := NumericalCostExpression.input .branches
  let d := NumericalCostExpression.input .dimension
  let v := NumericalCostExpression.input .vertices
  let G := NumericalCostExpression.input .parameter
  let K := NumericalCostExpression.input .iterations
  let t := NumericalCostExpression.input .history
  let Be := NumericalCostExpression.input .etaBits
  let Bk := NumericalCostExpression.input .kappaBits
  let Bm := NumericalCostExpression.input .massBits
  let Bt := NumericalCostExpression.input .tableBits
  let E := NumericalCostExpression.input .etaValue
  expressionBandPreparation M d v Bm + d * (expressionOnlineBit Be Bk Bm Bt t + 6) +
    expressionOptimizer d v G K (expressionBandVertexWord M Bm) (expressionBandVertexWord M Bm)
      (expressionOnlineStorage Be Bk Bm Bt t) (E * (2 * t + 1)) + 2

private def preparedCostEnvironment (M d v G K t Be Bk Bm Bt E : ℕ) : NumericalCostInput → ℕ
  | .branches => M
  | .dimension => d
  | .vertices => v
  | .parameter => G
  | .iterations => K
  | .history => t
  | .etaBits => Be
  | .kappaBits => Bk
  | .massBits => Bm
  | .tableBits => Bt
  | .etaValue => E
  | _ => 0

def preparedOptimizerBitPolynomialDegree : ℕ := preparedOptimizerCostExpression.degree

private theorem preparedOptimizerCostExpression_eval (M d v G K t Be Bk Bm Bt E : ℕ) :
    preparedOptimizerCostExpression.eval (preparedCostEnvironment M d v G K t Be Bk Bm Bt E) =
      BinaryFraction.preparedBandOptimizerBitBudget M d v G K t Be Bk Bm Bt E := by
  have hnat : (BinaryFraction.nat G).width = max (Nat.size G) 1 := by
    simp only [BinaryFraction.nat, BinaryFraction.width, SignedBinary.ofInt,
      Int.natAbs_natCast, ← Nat.size_eq_bits_len, List.length_cons, List.length_nil]
  simp only [preparedOptimizerCostExpression, preparedCostEnvironment,
    expressionBandSumStorage, expressionBandVertexWord, expressionStoredSumWord,
    expressionStoredSumBit, expressionBandCoordinateBit, expressionBandPreparation,
    expressionOptimisticStorage, expressionOnlineStorage, expressionGainBit,
    expressionDecrementBit, expressionCoefficientBit, expressionOptimisticBit, expressionOnlineBit,
    expressionOptimizer, expressionPoint, expressionGradientStorage,
    expressionGradientBit, expressionLogStorage, expressionLogBit, expressionLogUniversal,
    expressionLogStep, expressionMaximizer, expressionUpdate, costSize, costMax,
    NumericalCostExpression.eval, BinaryFraction.preparedBandOptimizerBitBudget,
    BinaryFraction.bandPreparationBitBudget, BinaryFraction.storedSumBitBudget,
    BinaryFraction.storedSumWordBudget, BinaryFraction.bandCoordinateBitBudget,
    BinaryFraction.bandMassTotalStorageBudget, BinaryFraction.bandVertexWordBudget,
    BinaryFraction.onlineLinearBitBudget, BinaryFraction.coefficientBitBudget,
    BinaryFraction.optimisticTermBitBudget, BinaryFraction.optimisticTermWordBudget,
    BinaryFraction.decrementBitBudget, BinaryFraction.gainBitBudget,
    BinaryFraction.optimisticTermStorageBudget, BinaryFraction.onlineFinalWordBudget,
    BinaryFraction.onlineLinearStorageBudget,
    BinaryFraction.optimizerBitBudget, BinaryFraction.optimizerRoundBitBudget,
    BinaryFraction.optimizerPointWordBudget, BinaryFraction.optimizerGradientWordBudget,
    UnreducedRational.gradientStorageBudget, UnreducedRational.logarithmStorageBudget,
    BinaryFraction.gradientCellBitBudget, BinaryFraction.generalPowerWordBudget,
    BinaryFraction.smoothingStorageBudget, BinaryFraction.shiftedStorageBudget,
    BinaryFraction.gradientLogStorageBudget, BinaryFraction.logarithmBitBudget,
    BinaryFraction.logarithmUniversalWordBudget, BinaryFraction.logarithmPartialBitStep,
    BinaryFraction.maximizerBitBudget, BinaryFraction.maximizerWordBudget, BinaryFraction.dotWordBudget,
    BinaryFraction.optimizerUpdateBitBudget, BinaryFraction.updateCoordinateWordBudget,
    BinaryFraction.updateCoefficientWordBudget, hnat]
  rfl

theorem preparedBandOptimizerBitBudget_le_fixed_power (M d v G K t Be Bk Bm Bt E S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hd : d ≤ S) (hv : v ≤ S) (hG : G ≤ S) (hK : K ≤ S)
    (ht : t ≤ S) (hBe : Be ≤ S) (hBk : Bk ≤ S) (hBm : Bm ≤ S) (hBt : Bt ≤ S) (hE : E ≤ S) :
    BinaryFraction.preparedBandOptimizerBitBudget M d v G K t Be Bk Bm Bt E ≤
      S ^ preparedOptimizerBitPolynomialDegree := by
  rw [← preparedOptimizerCostExpression_eval]
  apply NumericalCostExpression.eval_le_pow _ _ S hS
  intro i
  cases i <;> first | assumption | exact Nat.zero_le _

end EditApproximation

end OAI
