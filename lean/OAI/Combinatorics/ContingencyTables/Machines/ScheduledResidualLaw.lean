import OAI.Combinatorics.ContingencyTables.Machines.ScheduledCountSemantics
import OAI.Combinatorics.ContingencyTables.Machines.ScheduledResidualProgram
import OAI.Combinatorics.ContingencyTables.Sampling.CompiledResidualCorrection

namespace OAI

/-! # Correctness and positivity of the executed correction vector -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms OriginalTableBox ResidualMixture FirstSuccess CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

lemma scheduledCounts_domination
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    ∀ X,(1-1/((2^D:ℕ):ℚ))*
      ((scheduledCountsLaw r c htotal (2*D)).toRational
        (pow_pos (scheduledTrialDenominator_pos _) _)).mass X≤uniformMass (α := Table r c) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  dsimp only
  rw [scheduledCountsLaw_law]
  obtain ⟨residual,hr⟩ := scheduled_residual_correction r c hPL hCheeger htotal
  intro X
  have hn : 0≤(1/(2:ℚ)^D)*residual.mass X :=
    mul_nonneg (by positivity) (residual.nonnegative X)
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  linarith [hr X]

/-- The explicit correction vector is the embedded integer residual law. -/
theorem scheduledResidualCounts_actual
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    scheduledResidualCounts (((List.ofFn r,List.ofFn c),2*D),2^D)=
      List.ofFn ((IntegerResidualCorrection.law (scheduledCountsLaw r c htotal (2*D)) (2^D)
        (pow_pos (scheduledTrialDenominator_pos _) _) (by positivity)
        (scheduledCounts_domination r c hPL hCheeger htotal)).push (index r c le_rfl)).count := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  dsimp only
  unfold scheduledResidualCounts cachedResidualCounts cachedResidualInput scheduledResidualCache
  rw [scheduledCounts_actual r c htotal,List.sum_ofFn,(IntegerLaw.push _ _).total]
  exact OriginalBoxLaw.residualVector_law r c _ (GreedyFeasibleTable.table r c htotal) _
    (pow_pos (scheduledTrialDenominator_pos _) _) (by positivity)
    (scheduledCounts_domination r c hPL hCheeger htotal)

/-- Positive total weight makes the exact weighted rejection loop applicable. -/
theorem scheduledResidualCounts_sum
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    0<(scheduledResidualCounts (((List.ofFn r,List.ofFn c),2*D),2^D)).sum := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  rw [scheduledResidualCounts_actual r c hPL hCheeger htotal,List.sum_ofFn,(IntegerLaw.push _ _).total]
  exact Nat.mul_pos Fintype.card_pos (pow_pos (scheduledTrialDenominator_pos _) _)

end
end ContingencyTables.SmallGraphProfiles

end OAI
