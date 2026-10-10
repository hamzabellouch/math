import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGridWork
import OAI.Combinatorics.EditApproximation.Binary.BinarySeedMedianWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryWarmupAverage
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial
import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Binary.BinaryCachedShellWork

namespace OAI

/-! Fixed degrees for the literal initial grid/minimum, trimmed seed
median, and child warmup average. Grid side length is an explicit input. -/

namespace EditApproximation

private abbrev IP := FiniteBitPolynomial (Fin 2)
private def ipCenter (B : IP) : IP :=
  2100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 11) ^ 2 + 1) + 2 * B + 5
private def ipScale (B : IP) : IP :=
  4000 * (B + 1) ^ 2 + 4000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    2 * (1000 * (64 * B + 45) ^ 2 + 1) + 2 * B + 7
private def ipGrid (L B : IP) : IP := 1000 * (B + 2) ^ 2 + L * (100 * (B + 3) ^ 2 + 5)
private def ipBox (L B : IP) : IP :=
  96 * (B + 1) + 2 * ipGrid L (B + 2) + L * (L * (16 * (B + 2) + 11) + L + 3) + 6
private def ipGridScale (L B : IP) : IP :=
  100 * (B + 6) ^ 2 + ipBox L (B + 5) + L ^ 2 * (ipCenter (B + 4) + 3) + 2
private def ipDistance (B : IP) : IP :=
  2 * (6000 * (B + 1) ^ 2 + 2) + 6000 * (8 * B + 7) ^ 2 + 4 * B + 3
private def ipGap (B : IP) : IP :=
  (6000 * (B + 1) ^ 2 + 1) + (6000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 2
private def ipConeInput (B : IP) : IP := B + (64 * B + 54) + (64 * B + 54)
private def ipSeed (B : IP) : IP :=
  2100 * (B + 2) ^ 2 + 500 * (4 * B + 5) ^ 2 + (1000 * (4 * B + 7) ^ 2 + 1) + B + 3
private def ipCone (B : IP) : IP :=
  ipGap B + ipSeed (ipConeInput B) + ipDistance B + 2000 * (ipConeInput B + 1) ^ 2 +
    6000 * (4 * ipConeInput B + 7) ^ 2 + 4
private def ipMinimumWord (B : IP) : IP := 128 * B + 90 + (32 * ipConeInput (40 * B + 22) + 54)
private def ipMinimum (n B : IP) : IP :=
  (8 * B + 2) + 2000 * (B + 1) ^ 2 + 6000 * (4 * B + 3) ^ 2 +
    2000 * (32 * B + 23) ^ 2 + n * (ipCone (40 * B + 22) + 3) +
    (1 + n * (1000 * (ipMinimumWord B + 1) ^ 2 + 2)) + 2 * B + 6
private def initialShellPolynomial : IP :=
  let B := .input 0
  let L := .input 1
  ((B + 1) * (B + 9) + 2 + (B + 1) * (ipScale (B + 4) + 3) +
    (B + 1) * (ipGridScale L B + L ^ 2 + 3) + 3) +
    ipMinimum ((B + 1) * L ^ 2) (B + 4) + 1

def preparedInitialBitDegree : ℕ := initialShellPolynomial.degree

private def cachedInitialShellPolynomial : IP :=
  initialShellPolynomial + (1 + 0 * (200 * ((0 + 1) * (1 + 1) + 1) ^ 2) +
    5000 * (ipMinimumWord (.input 0 + 4) + (0 * 1 + 1) + 2) ^ 2 + 1) + 1

def preparedCachedInitialBitDegree : ℕ := cachedInitialShellPolynomial.degree

theorem initialProgramBitBudget_fixedPower (P Amax B X : ℕ) (hX : 2 ≤ X)
    (hB : B ≤ X) (hL : 64 * Amax ^ 2 * P + 2 ≤ X) :
    BinaryFraction.initialProgramBitBudget P Amax B ≤ X ^ preparedInitialBitDegree := by
  let env : Fin 2 → ℕ := ![B, 64 * Amax ^ 2 * P + 2]
  have heval : initialShellPolynomial.eval env = BinaryFraction.initialProgramBitBudget P Amax B := by
    simp only [initialShellPolynomial, ipScale, ipGridScale, ipBox, ipGrid, ipCenter, ipMinimum,
      ipMinimumWord, ipConeInput, ipCone, ipSeed, ipGap, ipDistance, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> assumption
  rw [← heval]
  exact initialShellPolynomial.eval_le_pow env X hX henv

theorem cachedInitialProgramBitBudget_fixedPower (P Amax B X : ℕ) (hX : 2 ≤ X)
    (hB : B ≤ X) (hL : 64 * Amax ^ 2 * P + 2 ≤ X) :
    BinaryFraction.cachedInitialProgramBitBudget P Amax B ≤ X ^ preparedCachedInitialBitDegree := by
  let env : Fin 2 → ℕ := ![B, 64 * Amax ^ 2 * P + 2]
  have heval : cachedInitialShellPolynomial.eval env = BinaryFraction.cachedInitialProgramBitBudget P Amax B := by
    simp only [cachedInitialShellPolynomial, initialShellPolynomial, ipScale, ipGridScale, ipBox, ipGrid,
      ipCenter, ipMinimum, ipMinimumWord, ipConeInput, ipCone, ipSeed, ipGap, ipDistance,
      FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> assumption
  rw [← heval]
  exact cachedInitialShellPolynomial.eval_le_pow env X hX henv

private def medianShellPolynomial : IP :=
  let n := .input 0
  let B := .input 1
  let ceiling := 2000 * (B + 1) ^ 2 + 500 * (4 * B + 3) ^ 2 + B + 3
  (n * (ceiling + 3) + (n + 1) ^ 2 * (8 * (4 * B + 4) + 6) +
    n + 4 * (B + (4 * B + 4)) + 3 + B + 3) + 12 * B + 14

def preparedMedianBitDegree : ℕ := medianShellPolynomial.degree

theorem seedMedianBitBudget_fixedPower (n B X : ℕ) (hX : 2 ≤ X) (hn : n ≤ X) (hB : B ≤ X) :
    BinaryFraction.seedMedianBitBudget n B ≤ X ^ preparedMedianBitDegree := by
  let env : Fin 2 → ℕ := ![n, B]
  have heval : medianShellPolynomial.eval env = BinaryFraction.seedMedianBitBudget n B := by
    simp only [medianShellPolynomial, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> assumption
  rw [← heval]
  exact medianShellPolynomial.eval_le_pow env X hX henv

private def ipStoredSumWord (n B : IP) : IP :=
  (B + 1) + .bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
private def ipMassStorage (n B : IP) : IP := .bitLength n + B + 2 * (1 + n * (B + 1)) + 2
private def averageShellPolynomial : IP :=
  let n := .input 0
  let B := .input 1
  (1 + n * (100000 * (ipStoredSumWord n B + 1) ^ 2)) + 6 * n +
    2100 * (ipMassStorage n B + .bitLength n + 4) ^ 2 + .bitLength n + 2

def preparedAverageBitDegree : ℕ := averageShellPolynomial.degree

theorem warmupAverageBitBudget_fixedPower (n B X : ℕ) (hX : 2 ≤ X) (hn : n ≤ X) (hB : B ≤ X) :
    BinaryFraction.warmupAverageBitBudget n B ≤ X ^ preparedAverageBitDegree := by
  let env : Fin 2 → ℕ := ![n, B]
  have heval : averageShellPolynomial.eval env = BinaryFraction.warmupAverageBitBudget n B := by
    simp only [averageShellPolynomial, ipStoredSumWord, ipMassStorage, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> assumption
  rw [← heval]
  exact averageShellPolynomial.eval_le_pow env X hX henv

end EditApproximation

end OAI
