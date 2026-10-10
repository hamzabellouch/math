import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyRefinementCost
import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

namespace EditApproximation

private abbrev GP := FiniteBitPolynomial (Fin 6)

private def gp_storedSumWordBudget (n B : GP) : GP :=
  (B + 1) + FiniteBitPolynomial.bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

private def gp_storedSumBitBudget (n B : GP) : GP :=
  1 + n * (100000 * (gp_storedSumWordBudget n B + 1) ^ 2)

private def gp_bandMassTotalStorageBudget (M B : GP) : GP :=
  FiniteBitPolynomial.bitLength M + B + 2 * (1 + M * (B + 1)) + 2

private def gp_warmupAverageBitBudget (n B : GP) : GP :=
  gp_storedSumBitBudget n B + 6 * n +
    2100 * (gp_bandMassTotalStorageBudget n B + FiniteBitPolynomial.bitLength n + 4) ^ 2 + FiniteBitPolynomial.bitLength n + 2

private def gp_queryPhysicalDataBudget (T J B V C W : GP) : GP :=
  W + (T + 1 + T * (7 * J + 30 + (C + 1) + 3) + gp_warmupAverageBitBudget T V) +
    (8 * B + 7 * J + 32 + (C + 1)) + 1

private def gp_queryFamilySourceReadBudget (J B W : GP) : GP :=
  200 * (1000 * (B + 1) + 1000 + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W

private def gp_bitPowerBitBudget (n B : GP) : GP :=
  1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)

private def gp_powerDenominatorBitBudget (n A B : GP) : GP :=
  gp_bitPowerBitBudget n B + 5000 * (A + (n * B + 1) + 2) ^ 2 + 1

private def callbackPolynomial : GP :=
  gp_queryPhysicalDataBudget (.input 0) (.input 1) (.input 2) (.input 3) (.input 4)
    (gp_queryFamilySourceReadBudget (.input 1) (.input 2) (.input 5))

def queryCallbackShellDegree : ℕ := callbackPolynomial.degree

theorem queryCallbackShell_fixedPower (T J B V C W X : ℕ) (hX : 2 ≤ X)
    (hT : T ≤ X) (hJ : J ≤ X) (hB : B ≤ X) (hV : V ≤ X) (hC : C ≤ X) (hW : W ≤ X) :
    BinaryFraction.queryPhysicalDataBudget T J B V C (BinaryFraction.queryFamilySourceReadBudget J B W) ≤
      X ^ queryCallbackShellDegree := by
  have h := callbackPolynomial.eval_le_pow ![T, J, B, V, C, W] X hX (by
    intro i
    fin_cases i
    · exact hT
    · exact hJ
    · exact hB
    · exact hV
    · exact hC
    · exact hW)
  exact h

private def normalizationPolynomial : GP :=
  gp_powerDenominatorBitBudget (.input 0) (.input 1) (.input 2)

def queryNormalizationBitDegree : ℕ := normalizationPolynomial.degree

theorem queryNormalization_fixedPower (n A B X : ℕ) (hX : 2 ≤ X)
    (hn : n ≤ X) (hA : A ≤ X) (hB : B ≤ X) :
    BinaryFraction.powerDenominatorBitBudget n A B ≤ X ^ queryNormalizationBitDegree := by
  have h := normalizationPolynomial.eval_le_pow ![n, A, B, 0, 0, 0] X hX (by
    intro i
    fin_cases i
    · exact hn
    · exact hA
    · exact hB
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _)
  exact h

end EditApproximation

end OAI
