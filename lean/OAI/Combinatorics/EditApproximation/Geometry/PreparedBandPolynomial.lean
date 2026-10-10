import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedUnskippedWork
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

/-! A fixed-degree bound for the complete band constructor. The sole
non-polynomial quantity is the actual Cartesian-product list bound, an
explicit input subsequently bounded by the computed grid parameters. -/

namespace EditApproximation

private abbrev BP := FiniteBitPolynomial (Fin 8)
private def bpSumStorage (n B : BP) : BP := .bitLength n + B + 2 * (1 + n * (B + 1)) + 2
private def bpSumWord (n B : BP) : BP :=
  (B + 1) + .bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
private def bpSumWork (n B : BP) : BP := 1 + n * (100000 * (bpSumWord n B + 1) ^ 2)
private def bpConnectionWord (M B : BP) : BP := bpSumStorage (M + 1) (8 * B + 6)
private def bpConnectionWork (M B : BP) : BP :=
  (M + 1) * (6000 * (B + 1) ^ 2 + 4) + M * (2 * B + 6) +
    bpSumWork (M + 1) (8 * B + 6) + 6 * (M + 1) + 1
private def bpEndpointWord (M B : BP) : BP :=
  8 * (bpConnectionWord M B + bpSumStorage M B) + 6
private def bpEndpointWork (M B : BP) : BP :=
  bpConnectionWork M B + 2 * B + M + 2 + bpSumWork M B + 6 * M +
    6000 * (bpConnectionWord M B + bpSumStorage M B + 1) ^ 2 + 2
private def bpMinimum (M n B : BP) : BP :=
  bpEndpointWork M B + n * (bpEndpointWork M B + 3) +
    (1 + n * (1000 * (bpEndpointWord M B + 1) ^ 2 + 2)) + 2
private def bpGapWord (B : BP) : BP := 64 * B + 54
private def bpGapWork (B : BP) : BP :=
  (6000 * (B + 1) ^ 2 + 1) + (6000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 2
private def bpNaturalDistance (B : BP) : BP :=
  6000 * (B + 1) ^ 2 + 2 + (1000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 3
private def bpAnchor (B : BP) : BP :=
  2 * (36 * B + 4) + 80 * (B + 4) + 2 * bpNaturalDistance B + 3
private def bpTolerance (B : BP) : BP :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 + 2 * B + 3
private def bpPredicate (M B C : BP) : BP :=
  (M + 1) * (8 * B + 3) + M * (bpAnchor B + 3) + bpTolerance B + M * (C + 3) + 4
private def bpBand (n B C : BP) : BP :=
  6000 * (B + 1) ^ 2 + 1000 * (8 * B + 7) ^ 2 + n * (C + 3) + 4
private def bpRepresentative (M n B : BP) : BP :=
  let W := B + bpEndpointWord M B + bpGapWord B + 1
  let S := 4 * W + 4 + B + M + n + 2
  bpMinimum M n B + 1000 * (W + 1) ^ 2 + bpGapWork B + 2100 * (W + 2) ^ 2 +
    bpBand n (4 * W + 4) (bpPredicate M S (S ^ prefixArithmeticDegree)) + 3
private def bpGridPoints (n B : BP) : BP :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)
private def bpGridBox (n B : BP) : BP :=
  96 * (B + 1) + 2 * bpGridPoints n (B + 2) +
    n * (n * (16 * (B + 2) + 11) + n + 3) + 6
private def bpWide (M P B C : BP) : BP :=
  M * (10000 * (B + 12) ^ 2 + bpGridBox (40 * P + 2) (B + 12) + 6) +
    (M + 1) * (6 * M + 10) * C + 1
private def bpEnvelopeWord (M bb B : BP) : BP := B + bb + .bitLength M + 8
private def bpEnvelopeWork (M bb n B : BP) : BP :=
  let W := bpEnvelopeWord M bb B
  2100 * (bb + .bitLength M + 6) ^ 2 +
    (1 + n * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + n + 4
private def bpRound (M e bb n B : BP) : BP :=
  let W := e + 2 + 3 * bpEnvelopeWord M bb B + B
  M * (bpEnvelopeWork M bb n B +
    (2000 * (W + 1) ^ 2 + 1500 * (4 * W + 3) ^ 2 + 3) +
    500 * (4 * W + 4 + B + 1) ^ 2 + e + 11)
private def bpGuard (e bb M v w B : BP) : BP :=
  let E := 3 * bpEnvelopeWord M bb B + 1
  let W := B + E + bpSumStorage M E + bpGapWord B + 10
  M * (bpEnvelopeWork M bb v B + 6) + bpSumWork M E +
    2000 * (W + 1) ^ 2 + 2000 * (4 * W + 3) ^ 2 +
    (1000 * (16 * W + 11) ^ 2 + 1) + bpRound M e bb v B +
    (1 + w * (M * (16 * B + 8) + 1)) +
    M * (18 * B + 1 + bpGapWork B + 2000 * (W + 1) ^ 2 +
      (1000 * (4 * W + 3) ^ 2 + 1) + 6) + 5
private def preparedBandPolynomial : BP :=
  let M := .input 0
  let P := .input 1
  let e := .input 2
  let bb := .input 3
  let v := .input 4
  let w := .input 5
  let B := .input 6
  let C := .input 7
  2 * bpWide M P B C + bpRepresentative M w (4 * B + 20) + bpGuard e bb M v w B + 2 * w + 4

def preparedBandBitDegree : ℕ := preparedBandPolynomial.degree

private def preparedBandEnvironment (e b M P v w B : ℕ) : Fin 8 → ℕ
  | 0 => M
  | 1 => P
  | 2 => e
  | 3 => Nat.size b
  | 4 => v
  | 5 => w
  | 6 => B
  | _ => ((40 * P + 2) ^ 2 + 1) ^ (M + 1)

private theorem preparedBandPolynomial_eval (e b M P v w B : ℕ) :
    preparedBandPolynomial.eval (preparedBandEnvironment e b M P v w B) =
      BinaryFraction.preparedUnskippedBitBudget e b M P v w B := rfl

theorem preparedUnskippedBitBudget_fixedPower (e b M P v w B S : ℕ)
    (hS : 2 ≤ S) (he : e ≤ S) (hb : Nat.size b ≤ S) (hM : M ≤ S) (hP : P ≤ S)
    (hv : v ≤ S) (hw : w ≤ S) (hB : B ≤ S)
    (hC : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S) :
    BinaryFraction.preparedUnskippedBitBudget e b M P v w B ≤ S ^ preparedBandBitDegree := by
  have henv : ∀ i, preparedBandEnvironment e b M P v w B i ≤ S := by
    intro i
    fin_cases i <;> simp only [preparedBandEnvironment] <;> assumption
  simpa only [preparedBandPolynomial_eval, preparedBandBitDegree] using
    preparedBandPolynomial.eval_le_pow _ S hS henv

/-- The representative tail used to construct the actual online draw range. -/
def representativeCompleteBitDegree : ℕ :=
  (bpRepresentative (.input 0) (.input 1) (.input 2)).degree

theorem representativeCompleteBitBudget_fixedPower (M vertices B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hV : vertices ≤ X) (hB : B ≤ X) :
    BinaryFraction.representativeCompleteBitBudget M vertices B ≤ X ^ representativeCompleteBitDegree := by
  let env : Fin 8 → ℕ := ![M, vertices, B, 0, 0, 0, 0, 0]
  have heval : (bpRepresentative (.input 0) (.input 1) (.input 2)).eval env =
      BinaryFraction.representativeCompleteBitBudget M vertices B := by rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact FiniteBitPolynomial.eval_le_pow _ env X hX henv

end EditApproximation

end OAI
