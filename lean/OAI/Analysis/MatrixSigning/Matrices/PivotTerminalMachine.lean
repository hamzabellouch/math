import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotDecisionPorts
import OAI.Analysis.MatrixSigning.Matrices.PivotReplayLoop
import OAI.Analysis.MatrixSigning.Optimization.TerminalWitnessMachine

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def unitTerminal : Program 35 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  KS.W19.TerminalVectorReplace.unitProgram
def sparseTerminal : Program 35 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  KS.W19.TerminalWitnessMachine.program

def terminalSelect (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 35 :=
  ⟨if (heads 29).val = 1 then .left else .right, Vector.ofFn (fun _ => .stay)⟩
def terminalProgram : Program 35 := KS.W29.FixedBranch.branch unitTerminal sparseTerminal 23 terminalSelect

def terminalState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix n) (q : Fin n → ℚ) : Fin 35 → List Bool :=
  Function.update (matrixState saved M) 23 (KS.W12.RowDot.vectorTape q)

def unitTicks (n : ℕ) : ℕ :=
  KS.W19.TerminalZeroVector.ticks (n+1) + (KS.W19.TerminalVectorReplace.oneFrame.length+1+
    (2*((KS.W19.TerminalVectorReplace.zeroPayloads (n+1)).flatMap KS.W01.frame).length+
      2*KS.W19.TerminalVectorReplace.oneFrame.length+3))

theorem unitTerminal_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    RunSpec unitTerminal (Function.update (matrixState saved M) 29 [false])
      (terminalState saved M (Pi.single 0 1)) (2+unitTicks n) := by
  have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 35)
    (Function.update (matrixState saved M) 29 [false])
  have he : KS.W04.CleanRationalCompare.clearState 29
      (Function.update (matrixState saved M) 29 [false]) = matrixState saved M := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,matrixState,state,Function.update]
  rw [he] at hc
  have hu := KS.W19.TerminalVectorReplace.unit_spec (matrixState saved M) (n+1) (by omega)
    rfl rfl rfl rfl rfl rfl rfl
  rw [KS.W19.TerminalVectorReplace.unit_tape] at hu
  exact hc.compose hu

theorem sparseTerminal_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n) :
    RunSpec sparseTerminal
      (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true])
      (terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
      (2+KS.W19.TerminalWitnessMachine.ticks saved M b j.succ) := by
  have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 35)
    (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true])
  have he : KS.W04.CleanRationalCompare.clearState 29
      (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true]) =
      KS.W19.TerminalWitnessMachine.inputState saved M j.succ := by
    funext k; fin_cases k <;> simp [KS.W04.CleanRationalCompare.clearState,
      KS.W19.TerminalWitnessMachine.inputState,Function.update]
  rw [he] at hc
  have hs := KS.W19.TerminalWitnessMachine.full_spec saved M b hnum hden j.succ (Fin.succ_ne_zero j)
  have ho : KS.W19.TerminalWitnessMachine.outputState saved M j.succ =
      terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ) := by
    funext k; fin_cases k <;> simp [KS.W19.TerminalWitnessMachine.outputState,
      terminalState,matrixState,state,Function.update]
  rw [ho] at hs
  exact hc.compose hs

theorem terminal_unit_case {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    RunSpec terminalProgram (Function.update (matrixState saved M) 29 [false])
      (terminalState saved M (Pi.single 0 1)) ((2+unitTicks n)+1) := by
  apply KS.W06.RationalCompare.branch_spec_left unitTerminal sparseTerminal 23 terminalSelect
    _ _ _ _ (unitTerminal_spec saved M)
  intro coin
  simp [terminalSelect,observedHeads,KS.W29.topCode,Function.update,KS.W06.RationalCompare.stayActions]

theorem terminal_sparse_case {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n) :
    RunSpec terminalProgram
      (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true])
      (terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
      ((2+KS.W19.TerminalWitnessMachine.ticks saved M b j.succ)+1) := by
  apply KS.W06.RationalCompare.branch_spec_right unitTerminal sparseTerminal 23 terminalSelect
    _ _ _ _ (sparseTerminal_spec saved M b hnum hden j)
  intro coin
  simp [terminalSelect,observedHeads,KS.W29.topCode,Function.update,KS.W06.RationalCompare.stayActions]

theorem terminal_negative_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (hn : DenseRatMatrix.decode M 0 0 < 0) :
    RunSpec terminalProgram (withSaved saved (PivotDecision.result M))
      (terminalState saved M (Pi.single 0 1)) ((2+unitTicks n)+1) := by
  rw [PivotDecision.result_negative M hn]
  have he : withSaved saved (Function.update (PivotRowLoop.initial M) 29 [false]) =
      Function.update (matrixState saved M) 29 [false] := by
    funext j; fin_cases j <;> simp [withSaved,PivotRowLoop.initial,PivotRowLoop.state,
      matrixState,state,Function.update,Computability.encodeNat,Computability.encodeNum]
  rw [he]
  exact terminal_unit_case saved M

theorem terminal_sparse_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n)
    (hz : DenseRatMatrix.decode M 0 0 = 0)
    (hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    RunSpec terminalProgram (withSaved saved (PivotDecision.result M))
      (terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
      ((2+KS.W19.TerminalWitnessMachine.ticks saved M b j.succ)+1) := by
  rw [PivotDecision.result_sparse M j hz hj]
  have he : withSaved saved (PivotRowLoop.finished M j.succ.val true) =
      Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true] := by
    funext k; fin_cases k <;> simp [withSaved,PivotRowLoop.finished,
      KS.W19.TerminalWitnessMachine.inputState,Function.update]
  rw [he]
  exact terminal_sparse_case saved M b hnum hden j

def finishTerminal : Program 35 := compose
  (KS.W04.CleanRationalCompare.clearListProgram 23 [31,26]) restoreAllProgram

theorem finishTerminal_spec {n N : ℕ} (h : PivotHistory n N) (M : DenseRatMatrix n) (q : Fin n → ℚ) :
    RunSpec finishTerminal (terminalState (historyTape h) M q)
      (state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore q)))
      ((KS.W08.denseMatrixTape M).length+(Computability.encodeNat n).length+3+restoreTicks h q) := by
  have hc := KS.W04.CleanRationalCompare.clearList_spec (23 : Fin 35) [31,26]
    (terminalState (historyTape h) M q)
  have he : KS.W04.CleanRationalCompare.clearListState [31,26] (terminalState (historyTape h) M q) =
      state (historyTape h) [] [] [] (KS.W12.RowDot.vectorTape q) := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearListState_apply,
      terminalState,matrixState,state,Function.update]
  have ht : KS.W04.CleanRationalCompare.clearListTicks [31,26] (terminalState (historyTape h) M q) =
      (KS.W08.denseMatrixTape M).length+(Computability.encodeNat n).length+3 := by
    simp [KS.W04.CleanRationalCompare.clearListTicks,KS.W04.CleanRationalCompare.clearState,
      terminalState,matrixState,state,Function.update]
    omega
  rw [he,ht] at hc
  exact hc.compose (restoreAll_spec h q)

end KS.W17.FixedPSD

end

end OAI
