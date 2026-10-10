import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedCellGroupWork
import OAI.Combinatorics.EditApproximation.Binary.BinarySampledGroupPolynomial
import OAI.Combinatorics.EditApproximation.Geometry.PreparedBandPolynomial

namespace OAI

/-! A fixed-degree cap for the complete cell selector, including all band
construction and exact finite-count sampled scores. -/

namespace EditApproximation

private abbrev CP := FiniteBitPolynomial (Fin 4)
private def cpEligibility (B : CP) : CP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8
private def cpGridPoints (n B : CP) : CP :=
  2000000 * (B + 100) ^ 2 + n * (1000 * (B + 100) ^ 2 + 5)
private def cpCellStates (l r B : CP) : CP :=
  cpGridPoints l B + cpGridPoints r B + l * (r * (16 * (17 * B + 78) + 11) + r + 3) + 2
private def cpCellCenters (P B : CP) : CP :=
  100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 + cpCellStates P P (4 * B + 40) +
    P * P * (cpEligibility B + 3) + 3
private def cellGroupPolynomial : CP :=
  let M := .input 0
  let P := .input 1
  let B := .input 2
  let X := .input 3
  cpCellCenters P B + (P + 1) ^ 2 * (X ^ preparedBandBitDegree + 3) +
    (P + 1) ^ 2 * (X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3) +
    1 + 2 * X ^ sampledGroupBitDegree + 2 * B + 2 * M + 6 + 2

def preparedCellGroupBitDegree : ℕ := cellGroupPolynomial.degree

private def cellGroupEnvironment (M P B X : ℕ) : Fin 4 → ℕ
  | 0 => M
  | 1 => P
  | 2 => B
  | _ => X

private theorem cellGroupPolynomial_eval (M P B X : ℕ) :
    cellGroupPolynomial.eval (cellGroupEnvironment M P B X) =
      BinaryFraction.cellCentersBitBudget P P B + (P + 1) ^ 2 * (X ^ preparedBandBitDegree + 3) +
        (P + 1) ^ 2 * (X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3) +
        1 + 2 * X ^ sampledGroupBitDegree + 2 * B + 2 * M + 6 + 2 := rfl

theorem preparedCellGroupBitBudget_fixedPower (M T e b P B X : ℕ)
    (hX : 2 ≤ X) (hM : M ≤ X) (hT : T ≤ X) (he : e ≤ X) (hb : Nat.size b ≤ X)
    (hP : P ≤ X) (hB : B ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.preparedCellGroupBitBudget M T e b P B ≤ X ^ preparedCellGroupBitDegree := by
  let V := (40 * P + 2) ^ (2 * M)
  have hband := preparedUnskippedBitBudget_fixedPower e b M P V V B X hX he hb hM hP hV hV hB hCartesian
  have hmember := sampledMemberBitBudget_fixedPower M T e b V B X hX hM hT he hb hV hB
  have hr : BinaryFraction.roundedBandBitBudget e b M V B ≤ X ^ sampledGroupBitDegree := by
    apply le_trans _ hmember.2
    unfold BinaryFraction.sampledMemberBitBudget
    omega
  have hc : BinaryFraction.connectionBitBudget M B ≤ X ^ sampledGroupBitDegree := by
    apply le_trans _ hmember.2
    unfold BinaryFraction.sampledMemberBitBudget
    omega
  have hs : BinaryFraction.selectedGroupBitBudget M T e b ((P + 1) ^ 2) V B ≤
      (P + 1) ^ 2 * (X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3) +
        1 + 2 * X ^ sampledGroupBitDegree + 2 * B + 2 * M + 6 := by
    unfold BinaryFraction.selectedGroupBitBudget
    have hw := Nat.pow_le_pow_left (Nat.add_le_add_right hmember.1 1) 2
    have hm := Nat.mul_le_mul_left ((P + 1) ^ 2)
      (show BinaryFraction.sampledMemberBitBudget M T e b V B +
        1000 * (BinaryFraction.sampledMemberWordBudget M T b B + 1) ^ 2 + 3 ≤
          X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3 by
        exact Nat.add_le_add_right (Nat.add_le_add hmember.2 (Nat.mul_le_mul_left 1000 hw)) 3)
    omega
  have hmajor : BinaryFraction.preparedCellGroupBitBudget M T e b P B ≤
      cellGroupPolynomial.eval (cellGroupEnvironment M P B X) := by
    rw [cellGroupPolynomial_eval]
    unfold BinaryFraction.preparedCellGroupBitBudget
    have hp := Nat.mul_le_mul_left ((P + 1) ^ 2) (Nat.add_le_add_right hband 3)
    change BinaryFraction.cellCentersBitBudget P P B +
      (P + 1) ^ 2 * (BinaryFraction.preparedUnskippedBitBudget e b M P V V B + 3) +
      BinaryFraction.selectedGroupBitBudget M T e b ((P + 1) ^ 2) V B + 2 ≤ _
    omega
  have henv : ∀ i, cellGroupEnvironment M P B X i ≤ X := by
    intro i
    fin_cases i <;> simp only [cellGroupEnvironment] <;> omega
  exact hmajor.trans (cellGroupPolynomial.eval_le_pow _ X hX henv)

end EditApproximation

end OAI
