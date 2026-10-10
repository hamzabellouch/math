import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.OwnerData

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition
open IndependentSetsGames.Foundations.PCP

private theorem joinTraceTopFinal {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

private theorem normalizeEmptyAppend {A : Type*} (output : List Bool → A)
    (bits : List Bool) : output ([] ++ bits) = output bits :=
  congrArg output (List.nil_append bits)

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinTraceTopFinal (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinTraceTopFinal (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinTraceTopFinal (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

@[simp] theorem update_frame_output (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 8) replacement =
      frame { data with output := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    exact (update_frame_output (inputData t []) (fun _ => [])
      (counterStacks [] [] [] [])
      (PortTables.tableBits (PreprocessingRegularTables.regularize H t))).symm.trans
      (congrArg (fun stk : Tape → List Bool => Function.update stk (coreTape 8)
        (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (input_stacks_eq H t))
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end IndependentSetsGames.Foundations.Complexity.MachineRegularTable.Top

end OAI
