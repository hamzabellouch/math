import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalWarmupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedKernelWork
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

namespace EditApproximation

private abbrev GP := FiniteBitPolynomial (Fin 2)

private def gp_bandMassTotalStorageBudget (M B : GP) : GP :=
  FiniteBitPolynomial.bitLength M + B + 2 * (1 + M * (B + 1)) + 2

private def gp_connectionWordBudget (k B : GP) : GP :=
  gp_bandMassTotalStorageBudget (k + 1) (8 * B + 6)

private def gp_endpointDistanceWordBudget (B : GP) : GP :=
  64 * B + 54

private def gp_physicalContinuationInputBudget (M B : GP) : GP :=
  B + gp_connectionWordBudget M B + gp_endpointDistanceWordBudget B + 4 * B + 2

private def gp_bellmanActionWordBudget (M B : GP) : GP :=
  8 * (40 * B + 22 + gp_bandMassTotalStorageBudget M B) + 6

private def gp_localWarmupWordBudget (M B : GP) : GP :=
  let W := gp_physicalContinuationInputBudget M (B + 4)
  W + gp_bellmanActionWordBudget M W

private def gp_refinementUpdateWordBudget (B : GP) : GP :=
  32 * B + 28

private def gp_localContinuationInputBudget (M B : GP) : GP :=
  B + 2 * gp_bellmanActionWordBudget M B + 1

private def gp_localContinuationWordBudget (M B : GP) : GP :=
  gp_refinementUpdateWordBudget (gp_localContinuationInputBudget M B)

private def gp_preparedKernelWordBudget (M B : GP) : GP :=
  gp_localContinuationWordBudget M (gp_physicalContinuationInputBudget M (B + 4))

private def rawWordPolynomial : GP :=
  gp_localWarmupWordBudget (.input 0) (.input 1) + gp_preparedKernelWordBudget (.input 0) (.input 1)

def queryRawWordDegree : ℕ := rawWordPolynomial.degree

theorem queryRawWord_fixedPower (M B X : ℕ) (hX : 2 ≤ X) (hM : M ≤ X) (hB : B ≤ X) :
    BinaryFraction.localWarmupWordBudget M B + BinaryFraction.preparedKernelWordBudget M B ≤
      X ^ queryRawWordDegree := by
  exact rawWordPolynomial.eval_le_pow ![M, B] X hX (by
    intro i
    fin_cases i
    · exact hM
    · exact hB)

end EditApproximation

end OAI
