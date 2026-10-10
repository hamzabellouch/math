import OAI.Computability.BinPacking.Computation.MachineRegularTable

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularTable.Top

section

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

private theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
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
  have joined := joinTrace (f := advance (TM2.step (program H))) first second
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
  have joined := joinTrace (f := advance (TM2.step (program H))) first second
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
  joinTrace (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

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
    | inl i => (fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]); rfl
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
    rw [← input_stacks_eq]
    exact (update_frame_output (inputData t []) (fun _ => []) (counterStacks [] [] [] [])
      (PortTables.tableBits (PreprocessingRegularTables.regularize H t))).symm
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds

noncomputable def oldLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOriginalBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def ownerLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOwnerBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Header.timePolynomial internalDegree + oldLoopPolynomial + ownerLoopPolynomial +
    4 * Polynomial.X + 12 +
    Polynomial.C (7 * (ExpanderFamily.growth * (internalDegree + 4) + 4)) *
      (Polynomial.X + 1)

theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end BinPackingGames.Foundations.Complexity.MachineRegularTable.Top

namespace BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)

def rawProgram (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.Program Tape Label State where
  input := coreTape 0
  output := coreTape 8
  main := .header .init
  initial := readyState H
  code := MachineRegularTable.Top.program H

theorem sourceMachine_eq (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.sourceMachine (rawProgram H) =
      MachineRegularTable.Top.machine H := rfl

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ : Finset Tape).toList.filter (fun k => decide (k ≠ coreTape 8))

theorem cleanup_complete (H : PreprocessingRegularTables.BaseTable) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H).output := by
  simp [cleanupTapes, rawProgram]

noncomputable def terminalRun (H : PreprocessingRegularTables.BaseTable)
    (t : GraphTables.Table) :
    MachineCanonicalOutput.TerminalRun (rawProgram H) (GraphTables.tableBits t)
      (PortTables.inputBits (PreprocessingStageMaps.regular H t))
      (MachineRegularTable.Top.timePolynomial.eval (GraphTables.tableBits t).length) where
  state := readyState H
  tapes := Function.update
    (initList (MachineRegularTable.Top.machine H) (GraphTables.tableBits t)).stk
    (coreTape 8) (PortTables.inputBits (PreprocessingStageMaps.regular H t))
  execution := by
    simpa only [sourceMachine_eq, FinTM2.Cfg, FinTM2.step, MachineRegularTable.Top.machine,
      PreprocessingMachineBounds.inputLength, PreprocessingStageMaps.regular,
      PortTables.inputBits] using!
      MachineRegularTable.Top.machineInTime H t
  output_eq := by
    change Function.update _ (coreTape 8) _ (coreTape 8) = _
    exact Function.update_self _ _ _

noncomputable def computableInPolyTime (H : PreprocessingRegularTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingRegularTables.internalDegree + 1))
      (PreprocessingStageMaps.regular H) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

theorem finite_alphabet (H : PreprocessingRegularTables.BaseTable) :
    ∀ k, Finite ((computableInPolyTime H).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime

end OAI
