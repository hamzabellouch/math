import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RowDotControl
import OAI.Analysis.MatrixSigning.Machines.FixedDotMachine

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def initialStacks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    Fin 29 → List Bool :=
  state (KS.W08.denseMatrixTape M) (vectorTape x) (Computability.encodeNat i.val)
    (Computability.encodeNat n) [] [] []

def copyVector : Program 29 := copyProgram 20 23 (by decide) (by decide) (by decide)
def prepareProgram : Program 29 := compose copyVector loopProgram

def prepareTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  (2 * (vectorTape x).length + 2) + loopTicks M b i (indexedVector x)

theorem prepare_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) :
    RunSpec prepareProgram (initialStacks M x i)
      (boundary M x i [] n ((FixedDot.inputWire (rowPairs M i (indexedVector x))).reverse))
      (prepareTicks M b x i) := by
  have hc : RunSpec copyVector (initialStacks M x i)
      (boundary M x i (indexedVector x) 0 []) (2 * (vectorTape x).length + 2) := by
    convert copy_spec (20 : Fin 29) 23 (by decide) (by decide) (by decide)
      (initialStacks M x i) rfl rfl using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [initialStacks, boundary, state, put, Computability.encodeNat]
    rfl
  exact hc.compose (loop_spec M b hnum hden x i)

def clearCounter : Program 29 := KS.W04.BinaryStackMoves.clearProgram 24
def restoreWire : Program 29 := KS.W04.BinaryStackMoves.moveProgram 25 16
def dotPorts : Fin 19 ↪ Fin 29 := Fin.castLEEmb (by decide)
def dotProgram : Program 29 := KS.W29.FixedSequential.liftPorts FixedDot.program dotPorts

def finishProgram : Program 29 := compose (compose clearCounter restoreWire) dotProgram

def finishTicks (n : ℕ) (ps : List (ℚ × ℚ)) : ℕ :=
  ((Computability.encodeNat n).length + 1) + ((FixedDot.inputWire ps).length + 1) + FixedDot.totalTicks ps

theorem finish_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n)
    (ps : List (ℚ × ℚ)) :
    RunSpec finishProgram (boundary M x i [] n (FixedDot.inputWire ps).reverse)
      (put (initialStacks M x i) 17 (KS.W01.encodeRat (FixedDot.dotValue ps)))
      (finishTicks n ps) := by
  let s0 := boundary M x i [] n (FixedDot.inputWire ps).reverse
  let s1 := KS.W15.RationalMultiply.clearAfter 24 s0
  let s2 := KS.W15.RationalMultiply.moveAfter 25 16 s1
  have h1 := KS.W15.RationalMultiply.clear_spec (24 : Fin 29) s0
  have h2 := KS.W15.RationalMultiply.move_spec (25 : Fin 29) 16 (by decide) s1
  have h3 : RunSpec dotProgram s2
      (put (initialStacks M x i) 17 (KS.W01.encodeRat (FixedDot.dotValue ps)))
      (FixedDot.totalTicks ps) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (FixedDot.full_spec ps)
    · intro j
      fin_cases j <;> simp [s0, s1, s2, boundary, state, dotPorts,
        FixedDot.initialStacks, FixedDot.registers, KS.W15.RationalMultiply.clearAfter,
        KS.W15.RationalMultiply.moveAfter]
    · intro j
      fin_cases j <;> simp [put, initialStacks, state, dotPorts, FixedDot.boundary, FixedDot.registers]
    · intro j hj
      have h16 : j ≠ 16 := hj 16
      have h17 : j ≠ 17 := hj 17
      fin_cases j <;> simp_all [s0, s1, s2, put, initialStacks, boundary, state,
        KS.W15.RationalMultiply.clearAfter, KS.W15.RationalMultiply.moveAfter]
  have h := (h1.compose h2).compose h3
  simp [finishProgram, finishTicks, s0, s1, boundary, state,
    KS.W15.RationalMultiply.clearAfter] at h ⊢
  exact h

def program : Program 29 := compose prepareProgram finishProgram

def totalTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  prepareTicks M b x i + finishTicks n (rowPairs M i (indexedVector x))

theorem full_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) :
    RunSpec program (initialStacks M x i)
      (put (initialStacks M x i) 17 (KS.W01.encodeRat ((KS.W07.DenseRatMatrix.decode M *ᵥ x) i)))
      (totalTicks M b x i) := by
  have h := (prepare_spec M b hnum hden x i).compose
    (finish_spec M x i (rowPairs M i (indexedVector x)))
  simp only [rowPairs_dotValue] at h
  exact h

theorem transient_payload {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ)
    (i : Fin n) (bits : List Bool) (j : Fin 29) :
    ((program.toMachine.run ⟨some program.initial, initialStacks M x i⟩ bits).«stacks» j).length ≤
      (KS.W08.denseMatrixTape M).length + (vectorTape x).length +
      (Computability.encodeNat i.val).length + (Computability.encodeNat n).length + bits.length := by
  have h := program.toMachine.run_stack_length_le
    (⟨some program.initial, initialStacks M x i⟩ : Config 29 program.states) bits j
  have hs : ((initialStacks M x i) j).length ≤
      (KS.W08.denseMatrixTape M).length + (vectorTape x).length +
      (Computability.encodeNat i.val).length + (Computability.encodeNat n).length := by
    fin_cases j <;> simp [initialStacks, state] <;> omega
  exact h.trans (Nat.add_le_add_right hs _)

end KS.W12.RowDot

end OAI
