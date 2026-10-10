import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.ImmediateChildChartAssembly
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellDeficitAssembly

namespace OAI

/-!
# Lipschitz constants for restart-chart iteration

The step constant simultaneously bounds the inherited chart constant, one, and
the two constants needed for immediate-child and active-cell assembly. Iterating
this monotone envelope gives nondecreasing bounds for every finite restart depth.
-/

namespace RieszRectifiability

noncomputable section

open scoped NNReal

def restartChartStepConstant (d N : ℕ) (P M : ℝ≥0) : ℝ≥0 :=
  max M (max 1 (max (immediateChildAssemblyConstant d M)
    (activeCellFinitePieceAssemblyConstant d N P M)))

theorem restartChartStepConstant_bounds (d N : ℕ) (P M : ℝ≥0) :
    M ≤ restartChartStepConstant d N P M ∧
    1 ≤ restartChartStepConstant d N P M ∧
    immediateChildAssemblyConstant d M ≤ restartChartStepConstant d N P M ∧
    activeCellFinitePieceAssemblyConstant d N P M ≤ restartChartStepConstant d N P M := by
  unfold restartChartStepConstant
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_, ?_⟩
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem restartChartStepConstant_mono (d N : ℕ) (P : ℝ≥0) :
    Monotone (restartChartStepConstant d N P) := by
  intro M L hML
  unfold restartChartStepConstant immediateChildAssemblyConstant finiteBallChartUnionConstant
    activeCellFinitePieceAssemblyConstant separatedPatchGluingConstant
  gcongr

def restartChartIterationConstant (d N : ℕ) (P : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 1
  | t + 1 => restartChartStepConstant d N P (restartChartIterationConstant d N P t)

theorem restartChartIterationConstant_successor_bounds (d N : ℕ) (P : ℝ≥0) (t : ℕ) :
    restartChartIterationConstant d N P t ≤ restartChartIterationConstant d N P (t + 1) ∧
    1 ≤ restartChartIterationConstant d N P (t + 1) ∧
    immediateChildAssemblyConstant d (restartChartIterationConstant d N P t) ≤
      restartChartIterationConstant d N P (t + 1) ∧
    activeCellFinitePieceAssemblyConstant d N P (restartChartIterationConstant d N P t) ≤
      restartChartIterationConstant d N P (t + 1) :=
  restartChartStepConstant_bounds d N P (restartChartIterationConstant d N P t)

theorem restartChartIterationConstant_mono (d N : ℕ) (P : ℝ≥0) :
    Monotone (restartChartIterationConstant d N P) :=
  monotone_nat_of_le_succ (fun t => (restartChartIterationConstant_successor_bounds d N P t).1)

end

end RieszRectifiability

end OAI
