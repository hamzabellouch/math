import OAI.Combinatorics.EditApproximation.Binary.BinaryBandGuardWork
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

/-! Fixed-degree polynomial envelope for the literal prefix and band-test
arithmetic. The finite expression represents the bit counters;
its degree is independent of every input length and parameter. -/

namespace EditApproximation

private abbrev PE := FiniteBitPolynomial (Fin 4)

private def ps (a : PE) : PE := .bitLength a
private def pn (a b : PE) : PE := .minimum a b

private def peSumWord (n B : PE) : PE :=
  (B + 1) + ps n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
private def peSumBit (n B : PE) : PE := 1 + n * (100000 * (peSumWord n B + 1) ^ 2)
private def peSumStorage (n B : PE) : PE := ps n + B + 2 * (1 + n * (B + 1)) + 2
private def peConnectionWord (n B : PE) : PE := peSumStorage (n + 1) (8 * B + 6)
private def peConnectionBit (n B : PE) : PE :=
  (n + 1) * (6000 * (B + 1) ^ 2 + 4) + n * (2 * B + 6) +
    peSumBit (n + 1) (8 * B + 6) + 6 * (n + 1) + 1
private def pePrefixWord (M j B : PE) : PE :=
  8 * (peConnectionWord (pn j M) (8 * B + 6) + peSumStorage M B) + 6
private def pePrefixBit (M j B : PE) : PE :=
  6000 * (B + 1) ^ 2 + peConnectionBit (pn j M) (8 * B + 6) +
    peSumBit M B + 6 * M +
    6000 * (peConnectionWord (pn j M) (8 * B + 6) + peSumStorage M B + 1) ^ 2 +
    2 * B + 6 * M + 5
private def pePrefixMinimumBit (M j v B : PE) : PE :=
  pePrefixBit M j B + v * (pePrefixBit M j B + 3) +
    (1 + v * (1000 * (pePrefixWord M j B + 1) ^ 2 + 2)) + 1
private def peAffineBit (B : PE) : PE :=
  6000 * (B + 1) ^ 2 + 1 + 2000 * (B + 1) ^ 2 +
    (6000 * (12 * B + 9) ^ 2 + 1) + (1000 * (96 * B + 71) ^ 2 + 1) + 4
private def peCutWord (M j B : PE) : PE := pePrefixWord M j (8 * B + 6) + 76 * B + 50
private def peCutBit (M j v B : PE) : PE :=
  2 * (6000 * (B + 1) ^ 2 + 1) + pePrefixMinimumBit M j v (8 * B + 6) +
    peAffineBit (peCutWord M j B) + 4 * B + 6
private def peNaturalDistanceBit (B : PE) : PE :=
  6000 * (B + 1) ^ 2 + 2 + (1000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 3
private def peToleranceBit (B : PE) : PE :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 + 2 * B + 3
private def prefixAggregateExpression : PE :=
  let M := .input 0
  let j := .input 1
  let v := .input 2
  let B := .input 3
  pePrefixWord M j B + pePrefixBit M j B + pePrefixMinimumBit M j v B +
    peCutWord M j B + peCutBit M j v B + peNaturalDistanceBit B + peToleranceBit B

/-- Fixed degree of the prefix/guard arithmetic implementation. -/
def prefixArithmeticDegree : ℕ := prefixAggregateExpression.degree

private def prefixEnv (M j v B : ℕ) : Fin 4 → ℕ
  | 0 => M
  | 1 => j
  | 2 => v
  | _ => B

private theorem prefixAggregateExpression_eval (M j v B : ℕ) :
    prefixAggregateExpression.eval (prefixEnv M j v B) =
      BinaryFraction.prefixWordBudget M j B + BinaryFraction.prefixBitBudget M j B +
      BinaryFraction.prefixMinimumBitBudget M j v B + BinaryFraction.cutGuardWordBudget M j B +
      BinaryFraction.cutGuardBitBudget M j v B + BinaryFraction.naturalDistanceBitBudget B +
      BinaryFraction.bandToleranceBitBudget B := rfl

theorem prefix_guard_budgets_le_fixed_power (M j v B S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hj : j ≤ S) (hv : v ≤ S) (hB : B ≤ S) :
    BinaryFraction.prefixWordBudget M j B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.prefixBitBudget M j B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.prefixMinimumBitBudget M j v B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.cutGuardWordBudget M j B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.cutGuardBitBudget M j v B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.naturalDistanceBitBudget B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.bandToleranceBitBudget B ≤ S ^ prefixArithmeticDegree := by
  have henv : ∀ i, prefixEnv M j v B i ≤ S := by
    intro i
    fin_cases i <;> simp only [prefixEnv] <;> assumption
  have h := prefixAggregateExpression.eval_le_pow (prefixEnv M j v B) S hS henv
  rw [prefixAggregateExpression_eval] at h
  change _ ≤ S ^ prefixArithmeticDegree at h
  omega

end EditApproximation

end OAI
