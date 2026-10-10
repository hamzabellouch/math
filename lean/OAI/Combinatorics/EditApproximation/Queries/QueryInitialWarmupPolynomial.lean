import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmupCost
import OAI.Combinatorics.EditApproximation.Geometry.PreparedInitialPolynomial
import OAI.Combinatorics.EditApproximation.Geometry.PreparedWarmupPolynomial

namespace OAI

/-! Polynomial certificate for the complete initial and warmup dispatch,
including actual gathers, buffer scans, and the previous-pass median. -/

namespace EditApproximation

private abbrev GP := FiniteBitPolynomial (Fin 13)

private def gp_initialScaleGuardBitBudget (B : GP) : GP :=
  4000 * (B + 1) ^ 2 + 4000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    2 * (1000 * (64 * B + 45) ^ 2 + 1) + 2 * B + 7

private def gp_gridPointsBitBudget (n B : GP) : GP :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)

private def gp_gridStateBoxBitBudget (count B : GP) : GP :=
  96 * (B + 1) + 2 * gp_gridPointsBitBudget count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6

private def gp_queryGridPointsBitBudget (P K B : GP) : GP :=
  100 * (B + 2) ^ 2 + gp_gridStateBoxBitBudget (4 * K * P + 2) (B + 1) + 1

private def gp_queryInitialCentersBitBudget (P Amax B : GP) : GP :=
  let L := (64 * Amax ^ 2 * P + 2) ^ 2
  500 * (B + 1) ^ 2 + (B + 1) * (B + 9) + 2 +
    (B + 1) * (gp_initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (gp_queryGridPointsBitBudget P (16 * Amax ^ 2) (B + 2) + L + 3) + 2

private def gp_queryInitialSeedReadBudget (count B : GP) : GP :=
  16 * B + 7 + count * (16 * B + 6) + 500 * (B + 1) ^ 2

private def gp_queryInitialProgramBitBudget (aux : Fin 3 → GP) (P Amax B C : GP) : GP :=
  let count := (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2
  C + gp_queryInitialCentersBitBudget P Amax B + count * (C + 3) +
    (aux 0) * (gp_queryInitialSeedReadBudget count B + 2)

private def gp_queryChargedSeedBitBudget (aux : Fin 3 → GP) (copies J B C : GP) : GP :=
  8 * B + 3 + (7 * J + 33 + C) + copies + 1 +
    copies * (7 * J + 33 + C + 3) + (aux 1) + B + 1

private def gp_queryPhysicalInitialBitBudget (aux : Fin 3 → GP) (P __F Amax copies J symbolBits positionBits B C : GP) : GP :=
  30 * B + 20 + (10 * B + 2 * symbolBits + 4 * positionBits + B + 17) +
    (gp_queryInitialProgramBitBudget aux) P Amax B ((gp_queryChargedSeedBitBudget aux) copies J B C)

private def gp_localEligibilityBitBudget (B : GP) : GP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8

private def gp_queryExponentsBitBudget (B : GP) : GP :=
  (B + 1) * (gp_localEligibilityBitBudget (B + 4) + B + 5) + 2 * B + 3

private def gp_queryScalesBitBudget (B : GP) : GP :=
  gp_queryExponentsBitBudget B + (B + 1) * (B + 6) + 1

private def gp_queryRawCentersBitBudget (P F B : GP) : GP :=
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  gp_queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3

private def gp_queryWarmupRepresentatives (P F B : GP) : GP :=
  (B + 1) * (64 * F * P + 2) ^ 2

private def gp_localRepresentativeScaleBitBudget (P F B : GP) : GP :=
  let C := B + 4
  let L := 64 * F * P + 2
  100 * (C + 2) ^ 2 + gp_gridStateBoxBitBudget L C +
    L ^ 2 * (gp_localEligibilityBitBudget C + 3) + L ^ 2 * 4 + B + 6

private def gp_localRepresentativesBitBudget (P F B : GP) : GP :=
  gp_queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_localRepresentativeScaleBitBudget P F B + (64 * F * P + 2) ^ 2 + 3) + 3

private def gp_wideChildGridBitBudget (P B : GP) : GP :=
  10000 * (B + 12) ^ 2 + gp_gridStateBoxBitBudget (40 * P + 2) (B + 12)

private def gp_queryWideInputsBitBudget (M P count B : GP) : GP :=
  let G := (40 * P + 2) ^ 2
  let C := gp_wideChildGridBitBudget P (B + 1)
  count * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
    (count * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2

private def gp_queryWarmupInputsBitBudget (M P F B I : GP) : GP :=
  gp_localRepresentativesBitBudget P F B * (I + 2) +
    gp_queryWideInputsBitBudget M P (gp_queryWarmupRepresentatives P F B) B + 1

private def gp_queryWarmupParentReadBudget (P F B : GP) : GP :=
  16 * B + 7 + gp_queryWarmupRepresentatives P F B * (16 * B + 6)

private def gp_queryWarmupChildReadBudget (M P F B : GP) : GP :=
  1 + (gp_queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (24 * B + 9)

private def gp_queryWarmupProgramBitBudget (aux : Fin 3 → GP) (M P F B C : GP) : GP :=
  C + gp_queryRawCentersBitBudget P F B + gp_queryWarmupRepresentatives P F B * (C + 3) +
    gp_queryWarmupInputsBitBudget M P F B (gp_queryWarmupParentReadBudget P F B) +
    (gp_queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (C + 3) +
    (aux 2) *
      (gp_queryWarmupParentReadBudget P F B + M * (gp_queryWarmupChildReadBudget M P F B + 3) + 4)

private def gp_queryChargedWarmupBitBudget (aux : Fin 3 → GP) (M P F Amax copies J symbolBits positionBits B C : GP) : GP :=
  let I := (gp_queryPhysicalInitialBitBudget aux) P F Amax copies J symbolBits positionBits B C
  80 * (B + 1) + I +
    (gp_queryWarmupProgramBitBudget aux) M P F B (I + 7 * J + 33 + C)

private def initialWarmupPolynomial : GP :=
  gp_queryChargedWarmupBitBudget ![.input 10, .input 11, .input 12]
    (.input 0) (.input 1) (.input 2) (.input 3) (.input 4) (.input 5)
    (.input 6) (.input 7) (.input 8) (.input 9)

def queryInitialWarmupBitDegree : ℕ := initialWarmupPolynomial.degree

private def initialWarmupEnvironment (M P F Amax copies J symbolBits positionBits B C : ℕ) : Fin 13 → ℕ :=
  ![M, P, F, Amax, copies, J, symbolBits, positionBits, B, C,
    BinaryFraction.cachedInitialProgramBitBudget P Amax (B + 2),
    BinaryFraction.seedMedianBitBudget copies B, BinaryFraction.localWarmupBitBudget M P F B]

private theorem initialWarmupPolynomial_eval (M P F Amax copies J symbolBits positionBits B C : ℕ) :
    initialWarmupPolynomial.eval (initialWarmupEnvironment M P F Amax copies J symbolBits positionBits B C) =
      queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C := by
  rfl

theorem queryChargedWarmupBitBudget_fixedPower (M P F Amax copies J symbolBits positionBits B C X : ℕ)
    (hX : 2 ≤ X)
    (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (hA : Amax ≤ X) (hc : copies ≤ X)
    (hJ : J ≤ X) (hs : symbolBits ≤ X) (hp : positionBits ≤ X) (hB : B ≤ X) (hC : C ≤ X)
    (hi : BinaryFraction.cachedInitialProgramBitBudget P Amax (B + 2) ≤ X)
    (hm : BinaryFraction.seedMedianBitBudget copies B ≤ X)
    (hw : BinaryFraction.localWarmupBitBudget M P F B ≤ X) :
    queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C ≤
      X ^ queryInitialWarmupBitDegree := by
  rw [← initialWarmupPolynomial_eval]
  apply initialWarmupPolynomial.eval_le_pow _ X hX
  intro i
  fin_cases i
  · exact hM
  · exact hP
  · exact hF
  · exact hA
  · exact hc
  · exact hJ
  · exact hs
  · exact hp
  · exact hB
  · exact hC
  · exact hi
  · exact hm
  · exact hw

end EditApproximation

end OAI
