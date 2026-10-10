import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotDecisionCorrectness
import OAI.Analysis.MatrixSigning.Optimization.PivotDescentMachine

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def withSaved (saved : List Bool) (small : Fin 32 → List Bool) : Fin 35 → List Bool :=
  fun j => if h : j.val < 32 then small ⟨j.val,h⟩ else if j=32 then saved else []

def decisionProgram : Program 35 := liftPorts PivotDecision.program schurPorts

@[simp] theorem withSaved_initial {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    withSaved saved (PivotRowLoop.initial M) = matrixState saved M := by
  funext j; fin_cases j <;>
    simp [withSaved,PivotRowLoop.initial,PivotRowLoop.state,matrixState,state,Computability.encodeNat,Computability.encodeNum]

theorem decision_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec decisionProgram (matrixState saved M) (withSaved saved (PivotDecision.result M))
      (PivotDecision.ticks M b) := by
  rw [← withSaved_initial saved M]
  apply KS.W01.FixedPortRunSpec.lift_runSpec PivotDecision.program schurPorts _ _ _ _ _
    (PivotDecision.full_spec M b hnum hden)
  · intro i; simp [withSaved,schurPorts,i.isLt]
  · intro i; simp [withSaved,schurPorts,i.isLt]
  · intro j hj
    have hge : ¬j.val<32 := by
      intro h
      exact hj ⟨j.val,h⟩ (Fin.ext rfl)
    simp [withSaved,hge]

theorem decision_nonterminal_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    RunSpec decisionProgram (matrixState saved M) (matrixState saved M) (PivotDecision.ticks M b) := by
  simpa only [PivotDecision.result_nonterminal M ht,withSaved_initial] using decision_spec saved M b hnum hden

end KS.W17.FixedPSD

end

end OAI
