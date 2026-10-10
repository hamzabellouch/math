import OAI.Computability.UniqueGames.Machines.MachineExpanderFamilyLoop

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

private def singleFamilyStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

/-- Complete initialization, actual counted loop, and normalized halt. -/
noncomputable def familyInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      (familyBudget H level) := by
  let loop := levelLoopInTime positive H growth 0 level
    (initialState positive H (caller state)) suffix
  have initialRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩) 1 :=
    singleFamilyStep _ _ _ (initialize_boundaryStep positive H growth level suffix state)
  have finalCaller : caller loop.finalState = caller state := loop.caller_preserved
  have done : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩) 1 := by
    simpa only [normalizeState, finalCaller] using
      singleFamilyStep _ _ _ (doneStep positive H growth (familyTapes H level suffix)
        loop.finalState)
  have loopRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩
      (some ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩)
      (levelLoopCost H 0 level) := by simpa only [Nat.zero_add] using loop.execution
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ initialRun loopRun
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ first done
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  have bound := all.steps_le_m
  have costEquality := levelLoopCost_zero_start H level
  unfold familyBudget
  omega

/-- The actual complete computation is polynomial in the final full vertex
count; the level is never silently treated as an equally long input. -/
noncomputable def familyInOutputSizeTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      ((resizeCoefficient d + 4) * (vertexCount (degree d) level + 1)^5) where
  toEvalsTo := (familyInTime positive H growth level state suffix).toEvalsTo
  steps_le_m := (familyInTime positive H growth level state suffix).steps_le_m.trans
    (familyBudget_le H growth level)

theorem baseDegree_cloud_growth :
    cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
  unfold cloudSize degree PCP.ExpanderFamily.growth
  ring

theorem baseDegree_cloud_gt_one : 1 < cloudSize PCP.Expanders.baseDegree := by
  rw [baseDegree_cloud_growth]
  exact PCP.ExpanderFamily.growth_gt_one

theorem baseDegree_positive : 0 < PCP.Expanders.baseDegree := by
  have h := baseDegree_cloud_gt_one
  unfold cloudSize degree at h
  by_contra hn
  have hz : PCP.Expanders.baseDegree = 0 := by omega
  rw [hz] at h
  norm_num at h

/-- At the physically computable padding level, the actual family run has a
fixed polynomial bound in requested unary size. The separate ceiling-power
machine supplies this exact level and preserves the requested size. -/
noncomputable def paddedFamilyInTime {ρ : Type} [Fintype ρ]
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree)
    (requested : Nat) (state : State ρ PCP.Expanders.baseDegree) (suffix : List Bool) :
    StateTransition.EvalsToInTime
      (TM2.step (program baseDegree_positive H baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize), state,
        initialTapes (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩
      (some ⟨none, initialState baseDegree_positive H (caller state),
        familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩)
      (inputCoefficient * (requested + 1)^5) where
  toEvalsTo := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).toEvalsTo
  steps_le_m := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).steps_le_m.trans
      (familyBudget_at_boundedLevel_le H requested)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
