import OAI.Combinatorics.ContingencyTables.Sampling.ExactSamplingParameters
import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixTrial
import OAI.Combinatorics.ContingencyTables.Machines.ScheduledResidualLaw

namespace OAI

/-! # Computing the complete input to the exact matrix rejection loop -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] exactResidualInput scheduledResidualCounts originalCandidates

def exactRareMeasure (z : CompletionMargins) : ℕ :=
  exactParameterMeasure z+scheduledResidualMeasure (exactResidualInput z)+
    originalEnumerationMeasure z+weight z

def exactRareWeights (z : CompletionMargins) : List ℕ :=
  scheduledResidualCounts (exactResidualInput z)

def exactRareWeightsRealizer : Realizer exactRareWeights :=
  composition (f := exactResidualInput) (g := scheduledResidualCounts)
    exactResidualInputRealizer scheduledResidualCountsRealizer

lemma work_exactRareWeights : WorkBound exactRareWeightsRealizer exactRareMeasure := by
  unfold exactRareWeightsRealizer
  have hp : WorkBound exactResidualInputRealizer exactRareMeasure :=
    work_remeasure work_exactResidualInput X (by
      intro z
      simp only [eval_X,exactRareMeasure]
      omega)
  apply work_composition hp work_scheduledResidualCounts X
  intro z
  simp only [eval_X,exactRareMeasure]
  omega

attribute [local irreducible] exactRareWeights

def exactMatrixInput (z : CompletionMargins) : ExactMatrixTrial.Input :=
  ((originalCandidates z,GreedyFeasibleTable.listMatrix z.1 z.2),exactRareWeights z)

def exactMatrixInputRealizer : Realizer exactMatrixInput :=
  pair (pair originalCandidatesRealizer GreedyFeasibleTable.tableRealizer) exactRareWeightsRealizer

lemma work_exactMatrixInput : WorkBound exactMatrixInputRealizer exactRareMeasure := by
  have hi (z : CompletionMargins) : weight z ≤ X.eval (exactRareMeasure z) := by
    simp only [eval_X,exactRareMeasure]
    omega
  have he : WorkBound originalCandidatesRealizer exactRareMeasure :=
    work_remeasure work_originalCandidates X (by
      intro z
      simp only [eval_X,exactRareMeasure]
      omega)
  exact work_pair (work_pair he (work_of_polynomial GreedyFeasibleTable.polynomial_table X hi) X hi)
    work_exactRareWeights X hi

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms OriginalTableBox ResidualMixture FirstSuccess CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

lemma exactRareWeights_pos
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    0<(exactRareWeights (List.ofFn r,List.ofFn c)).sum := by
  rw [exactRareWeights,exactResidualInput_ofFn]
  exact scheduledResidualCounts_sum r c hPL hCheeger htotal

lemma exactMatrixInput_code (htotal : (∑ i,r i)=∑ j,c j) :
    exactMatrixInput (List.ofFn r,List.ofFn c)=
      ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode (GreedyFeasibleTable.table r c htotal).val),
        scheduledResidualCounts (((List.ofFn r,List.ofFn c),2*D),2^D)) := by
  unfold exactMatrixInput exactRareWeights
  rw [exactResidualInput_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
