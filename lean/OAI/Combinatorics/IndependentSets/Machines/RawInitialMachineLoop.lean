import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Machine2
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineCleanup
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineFinish

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineLoop

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

def finalSigns {n : Nat} (incoming : RawInitialMachineModel.Signs) :
    List (Clause n) → RawInitialMachineModel.Signs
  | [] => incoming
  | c :: cs => finalSigns (RawInitialRows.clauseSigns c) cs

private theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem empty_loopTapes (n i : Nat) (rev : List Bool) :
    loopTapes n i 0 [] rev = finishTapes n i rev := by
  funext tape
  cases tape <;> rfl

theorem loopTrace {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[loopTime i cs]
      (some ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩) =
      some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩ := by
  induction cs generalizing i rev state with
  | nil =>
      have h := RawInitialMachineBody.guardTrace_zero n i [] rev state
      rw [empty_loopTapes] at h
      simpa only [loopTime, List.length_nil, clauseInput_nil, clauseOutput_nil,
        finalSigns, encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero,
        empty_loopTapes] using h
  | cons c cs ih =>
      have first := bodyTrace i cs.length c (clauseInput cs) rev state
      have rest := ih (i + 1)
        ((encodeWords (RawInitialRows.clauseWords n i
          (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ rev)
        (RawInitialRows.clauseSigns c, none)
      have total := trace_trans _ first rest
      have hi : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simpa only [loopTime, List.length_cons, clauseInput_cons, clauseOutput_cons,
        encodeWords_append, List.reverse_append, List.append_assoc, finalSigns, hi] using total

def loopInTime {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩
      (some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩)
      (loopTime i cs) where
  steps := loopTime i cs
  evals_in_steps := loopTrace i cs rev state
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.PCP.RawInitialMachineLoop
namespace IndependentSetsGames.Foundations.PCP.MachineRawInitialTable

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

private theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def prefixBits (F : Formula) : List Bool :=
  encodeWords ([F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
    clauseOutput F.«variables» 0 F.clauses)

theorem outputBits (F : Formula) :
    GraphTables.tableBits (RawInitialTables.table F) = prefixBits F ++
      encodeWords (RawInitialRows.dummyWords F.«variables» F.clauses.length) := by
  change encodeWords (GraphTables.tableWords (RawInitialTables.table F)) = _
  rw [tableWords_decomposition, encodeWords_append]
  rfl

theorem machineTrace (F : Formula) :
    (MachineComposition.advance (TM2.step program))^[fullBudget F]
      (some (initList machine (formulaBits F))) =
      some (haltList machine (GraphTables.tableBits (RawInitialTables.table F))) := by
  have startup := RawInitialMachineStart.formulaStartTrace F
  rw [startTapes_eq] at startup
  have loop := loopTrace 0 F.clauses
    (encodeWords [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse
    initialState
  have hprefix : (encodeWords (clauseOutput F.«variables» 0 F.clauses)).reverse ++
      (encodeWords [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse =
      (prefixBits F).reverse := by
    simp only [prefixBits, encodeWords_append, List.reverse_append]
  rw [hprefix, Nat.zero_add] at loop
  have finish := RawInitialMachineFinish.finishTrace F.«variables» F.clauses.length
    (prefixBits F).reverse (finalSigns initialState.1 F.clauses, none)
  rw [List.reverse_reverse, ← outputBits F] at finish
  have total := trace_trans _ (trace_trans _ startup loop) finish
  have time : (3 * F.«variables» + 5 * F.clauses.length + 13 + loopTime 0 F.clauses) +
      (3 * F.«variables» + 5 * F.clauses.length + 17 +
        (encodeWords (RawInitialRows.dummyWords F.«variables» F.clauses.length)).length +
        (prefixBits F).reverse.length) = fullBudget F := by
    rw [fullBudget, outputBits, List.length_append, List.length_reverse]
    omega
  simpa only [time] using total

def outputsInTime (F : Formula) :
    TM2OutputsInTime machine (formulaBits F)
      (some (GraphTables.tableBits (RawInitialTables.table F)))
      (timePolynomial.eval (formulaBits F).length) where
  steps := fullBudget F
  evals_in_steps := machineTrace F
  steps_le_m := fullBudget_le F

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaEncoding.encode GraphTables.encoding.encode
      RawInitialTables.table where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun F := by
    change TM2OutputsInTime machine ((formulaBits F).map id)
      (some ((GraphTables.tableBits (RawInitialTables.table F)).map id))
      (timePolynomial.eval (formulaBits F).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (formulaBits F)
    have ho := @List.map_id (machine.Γ machine.k₁)
      (GraphTables.tableBits (RawInitialTables.table F))
    rw [hi, ho]
    exact outputsInTime F

end IndependentSetsGames.Foundations.PCP.MachineRawInitialTable

end OAI
