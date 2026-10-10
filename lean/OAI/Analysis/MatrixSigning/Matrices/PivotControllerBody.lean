import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotTerminalMachine

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def terminalRestoreProgram : Program 35 := compose terminalProgram finishTerminal

def afterDecisionSelect (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 35 :=
  ⟨if (heads 29).val = 0 then .left else .right, Vector.ofFn (fun _ => .stay)⟩
def afterDecision : Program 35 := KS.W29.FixedBranch.branch fullDescendProgram terminalRestoreProgram 23 afterDecisionSelect

def controllerBody : Program 35 := compose decisionProgram afterDecision

def finishTicks {n N : ℕ} (h : PivotHistory n N) (M : DenseRatMatrix n) (q : Fin n → ℚ) : ℕ :=
  (KS.W08.denseMatrixTape M).length+(Computability.encodeNat n).length+3+restoreTicks h q

theorem body_descend_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    RunSpec controllerBody (matrixState saved M)
      (matrixState (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) ++ saved) (child M))
      (PivotDecision.ticks M b+(descentTicks M b+1)) := by
  have hd := fullDescend_spec saved M b hnum hden
  have hs : ∀ coin, afterDecisionSelect (observedHeads
      (⟨some (KS.W29.FixedBranch.start fullDescendProgram terminalRestoreProgram),matrixState saved M⟩ :
        Config 35 (fullDescendProgram.states+terminalRestoreProgram.states+1))) coin =
      ⟨.left,KS.W06.RationalCompare.stayActions 35⟩ := by
    intro coin; simp [afterDecisionSelect,matrixState,state,observedHeads,KS.W29.topCode,
      KS.W06.RationalCompare.stayActions]
  have hb := KS.W06.RationalCompare.branch_spec_left fullDescendProgram terminalRestoreProgram 23
    afterDecisionSelect _ _ _ hs hd
  exact (decision_nonterminal_spec saved M b hnum hden ht).compose hb

theorem body_negative_spec {n N : ℕ} (h : PivotHistory (n+1) N) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (hn : DenseRatMatrix.decode M 0 0 < 0) :
    RunSpec controllerBody (matrixState (historyTape h) M)
      (state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore (Pi.single 0 1))))
      (PivotDecision.ticks M b+(((2+unitTicks n)+1+finishTicks h M (Pi.single 0 1))+1)) := by
  have ht := (terminal_negative_spec (historyTape h) M hn).compose (finishTerminal_spec h M (Pi.single 0 1))
  have hs : ∀ coin, afterDecisionSelect (observedHeads
      (⟨some (KS.W29.FixedBranch.start fullDescendProgram terminalRestoreProgram),
        withSaved (historyTape h) (PivotDecision.result M)⟩ :
        Config 35 (fullDescendProgram.states+terminalRestoreProgram.states+1))) coin =
      ⟨.right,KS.W06.RationalCompare.stayActions 35⟩ := by
    intro coin
    rw [PivotDecision.result_negative M hn]
    simp [afterDecisionSelect,withSaved,observedHeads,KS.W29.topCode,Function.update,
      KS.W06.RationalCompare.stayActions]
  have hb := KS.W06.RationalCompare.branch_spec_right fullDescendProgram terminalRestoreProgram 23
    afterDecisionSelect _ _ _ hs ht
  exact (decision_spec (historyTape h) M b hnum hden).compose hb

theorem body_sparse_spec {n N : ℕ} (h : PivotHistory (n+1) N) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n)
    (hz : DenseRatMatrix.decode M 0 0 = 0)
    (hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    RunSpec controllerBody (matrixState (historyTape h) M)
      (state [] [] [] [] (KS.W12.RowDot.vectorTape
        (h.restore (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))))
      (PivotDecision.ticks M b+
        (((2+KS.W19.TerminalWitnessMachine.ticks (historyTape h) M b j.succ)+1+
          finishTicks h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))+1)) := by
  have ht := (terminal_sparse_spec (historyTape h) M b hnum hden j hz hj).compose
    (finishTerminal_spec h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
  have hs : ∀ coin, afterDecisionSelect (observedHeads
      (⟨some (KS.W29.FixedBranch.start fullDescendProgram terminalRestoreProgram),
        withSaved (historyTape h) (PivotDecision.result M)⟩ :
        Config 35 (fullDescendProgram.states+terminalRestoreProgram.states+1))) coin =
      ⟨.right,KS.W06.RationalCompare.stayActions 35⟩ := by
    intro coin
    rw [PivotDecision.result_sparse M j hz hj]
    simp [afterDecisionSelect,withSaved,PivotRowLoop.finished,observedHeads,KS.W29.topCode,
      KS.W06.RationalCompare.stayActions]
  have hb := KS.W06.RationalCompare.branch_spec_right fullDescendProgram terminalRestoreProgram 23
    afterDecisionSelect _ _ _ hs ht
  exact (decision_spec (historyTape h) M b hnum hden).compose hb

end KS.W17.FixedPSD

end

end OAI
