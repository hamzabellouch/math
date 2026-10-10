import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalOnlineWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuationWork
import OAI.Combinatorics.EditApproximation.Probability.FiniteBitPolynomial

namespace OAI

/-! Fixed-degree envelopes for the literal representative, online outer,
and continuation loops. Large action counts are explicit numeric inputs. -/

namespace EditApproximation

attribute [local irreducible] preparedBandBitDegree sampledOnlineBitDegree

private abbrev SP := FiniteBitPolynomial (Fin 8)
private def spGuard (B : SP) : SP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8
private def spGrid (n B : SP) : SP := 1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)
private def spBox (n B : SP) : SP :=
  96 * (B + 1) + 2 * spGrid n (B + 2) + n * (n * (16 * (B + 2) + 11) + n + 3) + 6
private def spQuery (B : SP) : SP := (B + 1) * (spGuard (B + 4) + B + 5) + 2 * B + 3
private def representativeShell : SP :=
  let P := .input 0
  let F := .input 1
  let B := .input 2
  let C := B + 4
  let L := 64 * F * P + 2
  spQuery B + 500 * (B + 1) ^ 2 +
    (B + 1) * (100 * (C + 2) ^ 2 + spBox L C + L ^ 2 * (spGuard C + 3) +
      L ^ 2 * 4 + B + 6 + L ^ 2 + 3) + 3

private def spCoordinates (M V B : SP) : SP :=
  V * (5 * M + 3) + (V * M + 1) ^ 2 * (24 * B + 12) + 1
private def spPower (n B : SP) : SP := 1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)
private def spOnline (M V B X : SP) : SP :=
  2 * X ^ preparedBandBitDegree + (spCoordinates M V B + 40 * (B + 4) + spPower 80 (B + 4) + 3) +
    (10000 * (B + 3) ^ 2 + 200 * (4 * B + 6) ^ 2 + B + 2) + X ^ sampledOnlineBitDegree + 3
private def onlineShell : SP :=
  let M := .input 0
  let V := .input 1
  let B := .input 2
  let X := .input 3
  let W := B + 4
  spQuery B + (B + 1) * (100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
    spGuard W + spOnline M V W X + B + 4 + 3) + 1

private def spSumStorage (n B : SP) : SP := .bitLength n + B + 2 * (1 + n * (B + 1)) + 2
private def spSumWord (n B : SP) : SP :=
  (B + 1) + .bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
private def spSumWork (n B : SP) : SP := 1 + n * (100000 * (spSumWord n B + 1) ^ 2)
private def spConnectionWord (M B : SP) : SP := spSumStorage (M + 1) (8 * B + 6)
private def spConnectionWork (M B : SP) : SP :=
  (M + 1) * (6000 * (B + 1) ^ 2 + 4) + M * (2 * B + 6) +
    spSumWork (M + 1) (8 * B + 6) + 6 * (M + 1) + 1
private def spActionWord (M B : SP) : SP := 8 * (40 * B + 22 + spSumStorage M B) + 6
private def spActionWork (M B C : SP) : SP :=
  C + 2000 * (B + 1) ^ 2 + 6000 * (5 * B + 3) ^ 2 + spSumWork M B + 6 * M +
    6000 * (40 * B + 22 + spSumStorage M B + 1) ^ 2 + 3
private def spBellman (M n B F C : SP) : SP :=
  n * (spActionWork M B C + 3) + (1 + n * (1000 * (F + spActionWord M B + 1) ^ 2 + 2)) + 1
private def spUpdate (B : SP) : SP :=
  6000 * (B + 1) ^ 2 + 2100 * (8 * B + 8) ^ 2 + 2 * (1000 * (32 * B + 29) ^ 2 + 1) + 2
private def spContinuation (M nw ng no B C : SP) : SP :=
  spBellman M nw B B C + spBellman M ng B (B + spActionWord M B) C +
    no * (spActionWork M B C + 3) + (2 + no * (1000 * (spActionWord M B + 1) ^ 2 + 2)) +
    spUpdate (B + 2 * spActionWord M B + 1) + 3
private def physicalShell : SP :=
  let M := .input 0
  let P := .input 1
  let nr := .input 2
  let ng := .input 3
  let no := .input 4
  let B := .input 5
  let V := .input 6
  let Cart := .input 7
  let wide := M * (10000 * (B + 12) ^ 2 + spBox (40 * P + 2) (B + 12) + 6) +
    (M + 1) * (6 * M + 10) * Cart + 1
  let W := B + spConnectionWord M B + (64 * B + 54) + 4 * B + 2
  let distance := 2 * (6000 * (B + 1) ^ 2 + 2) + 6000 * (8 * B + 7) ^ 2 + 4 * B + 3
  nr * (wide + V * (spConnectionWork M B + 2 * B + 2 * M + 6) + 1 + V + 3) +
    2000 * (B + 1) ^ 2 + spContinuation M (nr * V) ng no W distance + 1

def representativeShellDegree : ℕ := representativeShell.degree
def onlineShellDegree : ℕ := onlineShell.degree
def physicalShellDegree : ℕ := physicalShell.degree

theorem localRepresentativesBitBudget_fixedPower (P F B X : ℕ) (hX : 2 ≤ X)
    (hP : P ≤ X) (hF : F ≤ X) (hB : B ≤ X) :
    BinaryFraction.localRepresentativesBitBudget P F B ≤ X ^ representativeShellDegree := by
  let env : Fin 8 → ℕ := ![P, F, B, 0, 0, 0, 0, 0]
  have heval : representativeShell.eval env = BinaryFraction.localRepresentativesBitBudget P F B := by
    simp only [representativeShell, spQuery, spGuard, spBox, spGrid, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact representativeShell.eval_le_pow env X hX henv

theorem preparedLocalOnlineBitBudget_fixedPower (M P B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hB : B ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X) :
    BinaryFraction.preparedLocalOnlineBitBudget M P B X ≤ X ^ onlineShellDegree := by
  let env : Fin 8 → ℕ := ![M, (40 * P + 2) ^ (2 * M), B, X, 0, 0, 0, 0]
  have heval : onlineShell.eval env = BinaryFraction.preparedLocalOnlineBitBudget M P B X := by
    simp only [onlineShell, spQuery, spGuard, spOnline, spCoordinates, spPower, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact onlineShell.eval_le_pow env X hX henv

theorem physicalContinuationBitBudget_fixedPower (M P nr ng no B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hP : P ≤ X) (hr : nr ≤ X) (hg : ng ≤ X) (ho : no ≤ X) (hB : B ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.physicalContinuationBitBudget M P nr ng no B ≤ X ^ physicalShellDegree := by
  let env : Fin 8 → ℕ := ![M, P, nr, ng, no, B, (40 * P + 2) ^ (2 * M), ((40 * P + 2) ^ 2 + 1) ^ (M + 1)]
  have heval : physicalShell.eval env = BinaryFraction.physicalContinuationBitBudget M P nr ng no B := by
    simp only [physicalShell, spConnectionWord, spSumStorage, spBox, spGrid, spConnectionWork,
      spSumWork, spSumWord, spContinuation, spBellman, spActionWork, spActionWord, spUpdate,
      FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact physicalShell.eval_le_pow env X hX henv

end EditApproximation

end OAI
