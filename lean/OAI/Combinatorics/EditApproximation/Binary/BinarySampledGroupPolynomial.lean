import OAI.Combinatorics.EditApproximation.Binary.BinarySampledGroupWork
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

/-! A fixed polynomial bounds the actual sampled-member bit counter. The
scale is supplied through its bit length, so a large distance scale does
not introduce a spurious linear dependence on that scale. -/

namespace EditApproximation

private abbrev GP := FiniteBitPolynomial (Fin 6)
private def gbits (x : GP) : GP := .bitLength x
private def gSumWord (n B : GP) : GP :=
  (B + 1) + gbits n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
private def gSumWork (n B : GP) : GP := 1 + n * (100000 * (gSumWord n B + 1) ^ 2)
private def gSumStorage (n B : GP) : GP := gbits n + B + 2 * (1 + n * (B + 1)) + 2
private def gConnectionWord (M B : GP) : GP := gSumStorage (M + 1) (8 * B + 6)
private def gConnectionWork (M B : GP) : GP :=
  (M + 1) * (6000 * (B + 1) ^ 2 + 4) + M * (2 * B + 6) +
    gSumWork (M + 1) (8 * B + 6) + 6 * (M + 1) + 1
private def gEnvelopeWord (M bb B : GP) : GP := B + bb + gbits M + 8
private def gEnvelopeWork (M bb v B : GP) : GP :=
  let W := gEnvelopeWord M bb B
  2100 * (bb + gbits M + 6) ^ 2 + (1 + v * (1000 * (W + 1) ^ 2 + 2)) +
    (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + v + 4
private def gRoundWork (M e bb v B : GP) : GP :=
  let W := e + 2 + 3 * gEnvelopeWord M bb B + B
  M * (gEnvelopeWork M bb v B + (2000 * (W + 1) ^ 2 + 1500 * (4 * W + 3) ^ 2 + 3) +
    500 * (4 * W + 4 + B + 1) ^ 2 + e + 11)
private def gSampleCountWork (B : GP) : GP :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    500 * (64 * B + 45) ^ 2 + 4 * (65 * B + 46) + 3 * B + 8
private def gIndexWork (M B : GP) : GP :=
  M * (2 * (1000 * (B + 1) ^ 2 + 1) + 6) + gSumWork M B + 6 * M + 1
private def gScaleWord (M B : GP) : GP := 4 * (4 * B + 4 + gSumStorage M B) + 2
private def gScaleWork (M B : GP) : GP :=
  gIndexWork M B + (2100 * (B + 2) ^ 2 + 1) +
    2000 * (4 * B + 4 + gSumStorage M B + 1) ^ 2 + 2 * B + 3
private def gMemberWord (T B W : GP) : GP := 8 * (B + gSumStorage T W) + 6
private def gMemberWork (T B C W : GP) : GP :=
  T * (C + 3) + gSumWork T W + 6 * T + 6000 * (B + gSumStorage T W + 1) ^ 2 + 1
private def gCountedWork (M T B : GP) : GP :=
  T * (gSampleCountWork B + 6) + gMemberWork T B (gScaleWork M B) (gScaleWord M B) + 1
private def gInput (M bb B : GP) : GP :=
  B + (3 * gEnvelopeWord M bb B + 1) + gConnectionWord M B + 1

private def sampledGroupPolynomial : GP :=
  let M := .input 0
  let T := .input 1
  let e := .input 2
  let bb := .input 3
  let v := .input 4
  let B := .input 5
  gMemberWord T (gInput M bb B) (gScaleWord M (gInput M bb B)) +
    (M * (gEnvelopeWork M bb v B + 6) + gRoundWork M e bb v B + 7 * M +
      (gConnectionWork M B + 2 * B + M + 2) + gCountedWork M T (gInput M bb B) + 5)

def sampledGroupBitDegree : ℕ := sampledGroupPolynomial.degree

private def sampledGroupEnvironment (M T exponent b vertices B : ℕ) : Fin 6 → ℕ
  | 0 => M
  | 1 => T
  | 2 => exponent
  | 3 => Nat.size b
  | 4 => vertices
  | _ => B

private theorem sampledGroupPolynomial_eval (M T exponent b vertices B : ℕ) :
    sampledGroupPolynomial.eval (sampledGroupEnvironment M T exponent b vertices B) =
      BinaryFraction.sampledMemberWordBudget M T b B +
        BinaryFraction.sampledMemberBitBudget M T exponent b vertices B := rfl

theorem sampledMemberBitBudget_fixedPower (M T exponent b vertices B S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hT : T ≤ S) (he : exponent ≤ S)
    (hb : Nat.size b ≤ S) (hv : vertices ≤ S) (hB : B ≤ S) :
    BinaryFraction.sampledMemberWordBudget M T b B ≤ S ^ sampledGroupBitDegree ∧
      BinaryFraction.sampledMemberBitBudget M T exponent b vertices B ≤ S ^ sampledGroupBitDegree := by
  have henv : ∀ i, sampledGroupEnvironment M T exponent b vertices B i ≤ S := by
    intro i
    fin_cases i <;> simp only [sampledGroupEnvironment] <;> assumption
  have h := sampledGroupPolynomial.eval_le_pow (sampledGroupEnvironment M T exponent b vertices B) S hS henv
  rw [sampledGroupPolynomial_eval] at h
  exact ⟨(Nat.le_add_right _ _).trans h, (Nat.le_add_left _ _).trans h⟩

end EditApproximation

end OAI
