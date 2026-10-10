import Mathlib.Data.List.FinRange
import OAI.Computability.BinPacking.Computation.MachineCanonicalOutput
import OAI.Computability.BinPacking.Computation.MachineLazyRows
import OAI.Computability.BinPacking.Computation.MachineVertexPadding

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

inductive Tape
  | input | output | source | vertices | darts | fuel | vertex | reverse
  | tail | old | relation | scratch | divided | quotient | newReverse | rowBuffer
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .source, .vertices, .darts, .fuel,
  .vertex, .reverse, .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
  .rowBuffer]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (d : Nat) := MachineLazyRows.StreamState Unit d

def clean (d : Nat) (positive : 0 < d) : State d :=
  MachineLazyRows.streamClean d positive ()

theorem clean_pair (d : Nat) (positive : 0 < d) :
    ((clean d positive).1, (none : Option Bool)) = clean d positive := rfl

def splitRoles : Fin 5 → Tape := ![.input, .source, .scratch, .vertices, .darts]
def splitView : Tape → Option (Fin 5)
  | .input => some 0 | .source => some 1 | .scratch => some 2
  | .vertices => some 3 | .darts => some 4 | _ => none

def dummyRoles : Fin 6 → Tape := ![.tail, .reverse, .relation, .rowBuffer, .output, .scratch]
def dummyView : Tape → Option (Fin 6)
  | .tail => some 0 | .reverse => some 1 | .relation => some 2
  | .rowBuffer => some 3 | .output => some 4 | .scratch => some 5 | _ => none

def oldRoles : Fin 10 → Tape :=
  ![.tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
    .output, .rowBuffer, .source]

theorem splitRoles_left (i : Fin 5) : splitView (splitRoles i) = some i := by
  fin_cases i <;> rfl

theorem splitRoles_right (t : Tape) (i : Fin 5) (h : splitView t = some i) : splitRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [splitView, splitRoles]

theorem dummyRoles_left (i : Fin 6) : dummyView (dummyRoles i) = some i := by
  fin_cases i <;> rfl

theorem dummyRoles_right (t : Tape) (i : Fin 6) (h : dummyView t = some i) : dummyRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [dummyView, dummyRoles]

theorem oldRoles_injective : Function.Injective oldRoles := by decide

inductive Label (d : Nat)
  | split (label : MachineTableSplit.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | fuelFirst | fuelSecond | seedCounters | guard | copyVertexFirst | copyVertexSecond
  | dummy (label : MachineDummyRows.Label d)
  | clearDummyTail | clearDummyRelation
  | oldRows (label : MachineLazyRows.VertexLabel d)
  | nextVertex | clearVertices | clearDarts | clearFuel | clearVertex | clearReverse
  deriving DecidableEq, Fintype

def program (d : Nat) (positive : 0 < d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State d)
  | .split label => MachineCloudPadding.Placement.statement splitRoles Label.split
      (some .dartSeed) (MachineTableSplit.program label)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .darts .scratch .output 2 .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt .scratch .darts id false
      .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .vertices .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt .scratch .vertices id false
      .vertexRestore (some .fuelFirst)
  | .fuelFirst => Reduction.MachineTransfer.loopAt .vertices .scratch id false
      .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop .scratch .vertices .fuel false
      .fuelSecond (some .seedCounters)
  | .seedCounters => .push .vertex (fun _ => false)
      (.push .reverse (fun _ => false) (.goto fun _ => .guard))
  | .guard => MachineUnaryCounter.guard .fuel .copyVertexFirst .clearVertices
  | .copyVertexFirst => Reduction.MachineTransfer.loopAt .vertex .scratch id false
      .copyVertexFirst (some .copyVertexSecond)
  | .copyVertexSecond => MachineCopy.forkLoop .scratch .vertex .tail false
      .copyVertexSecond (some (.dummy (MachineDummyRows.start d)))
  | .dummy label => MachineCloudPadding.Placement.statement dummyRoles Label.dummy
      (some .clearDummyTail) (MachineDummyRows.program d label)
  | .clearDummyTail => MachineDrain.drain .tail .clearDummyTail (some .clearDummyRelation)
  | .clearDummyRelation => MachineDrain.drain .relation .clearDummyRelation (some (.oldRows (0, none)))
  | .oldRows label => MachineLazyRows.vertexInstruction d positive (2 * d) d oldRoles
      Label.oldRows (some .nextVertex) label
  | .nextVertex => pushWord .reverse (List.replicate d true)
      (.push .vertex (fun _ => true) (.goto fun _ => .guard))
  | .clearVertices => MachineDrain.drain .vertices .clearVertices (some .clearDarts)
  | .clearDarts => MachineDrain.drain .darts .clearDarts (some .clearFuel)
  | .clearFuel => MachineDrain.drain .fuel .clearFuel (some .clearVertex)
  | .clearVertex => MachineDrain.drain .vertex .clearVertex (some .clearReverse)
  | .clearReverse => MachineDrain.drain .reverse .clearReverse none

def frame (input source output vertices darts fuel vertex reverse : List Bool) : Tape → List Bool
  | .input => input | .source => source | .output => output
  | .vertices => vertices | .darts => darts | .fuel => fuel
  | .vertex => vertex | .reverse => reverse | _ => []

def initialTapes (input : List Bool) : Tape → List Bool := frame input [] [] [] [] [] [] []

def loopTapes (d : Nat) (input : List Bool) (n m left v : Nat)
    (source output : List Bool) : Tape → List Bool :=
  frame input source output (encodeWord n) (encodeWord m) (encodeWord left)
    (encodeWord v) (encodeWord (2 * d * v))

def finalTapes (input output : List Bool) : Tape → List Bool := frame input [] output [] [] [] [] []

private theorem joinTrace {X : Type} {f : X → X} {a b c : X} {s t : Nat}
    (first : f^[s] a = b) (second : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem dummyTrace (d : Nat) (positive : 0 < d) (base : Tape → List Bool) (v e : Nat)
    (ht : base .tail = encodeWord v) (he : base .reverse = encodeWord e)
    (hr : base .relation = []) (hb : base .rowBuffer = []) (hs : base .scratch = []) :
    (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v e (base .output) d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, base⟩) =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
          .relation MachineDummyRows.trueBits)
          .output (base .output ++ MachineDummyRows.rowsBits v e d)⟩ := by
  have initial : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.initialTapes v e (base .output)) base = base := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes, ht, he, hr, hb, hs]
  have final : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.fieldTapes v (e + d) (base .output ++ MachineDummyRows.rowsBits v e d))
      base = Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
        .relation MachineDummyRows.trueBits)
        .output (base .output ++ MachineDummyRows.rowsBits v e d) := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.fieldTapes, ht, hb, hs]
  have run := MachineCloudPadding.Placement.trace dummyRoles dummyView
    dummyRoles_left dummyRoles_right Label.dummy (some .clearDummyTail) base
    (MachineDummyRows.program d) (program d positive) (fun _ => rfl) _ _ _
    (MachineDummyRows.allTrace d v e (base .output) (clean d positive).1 none)
  simpa only [clean_pair, MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, initial, final] using run

theorem oldTrace {n m : Nat} (d : Nat) (positive : 0 < d)
    (base : Tape → List Bool) (rows : Fin d → GraphTables.DartRow n m) (rest : List Bool)
    (hi : base .source = MachineLazyRows.recordsInput (List.ofFn rows) ++ rest)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (oldRoles i) = []) :
    (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (base .output)]
      (some ⟨some (.oldRows (0, none)), clean d positive, base⟩) =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update base .source rest) .output
          (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows))⟩ := by
  let tailBase := Function.update base Tape.source rest
  have cleanBase : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → tailBase (oldRoles i) = [] := by
    intro i h7 h9
    have hn : oldRoles i ≠ Tape.source := by
      intro h
      have h' : oldRoles i = oldRoles 9 := h
      exact h9 (oldRoles_injective h')
    simpa only [tailBase, Function.update_of_ne hn] using empty i h7 h9
  have initial : MachineLazyRows.streamFrame oldRoles tailBase (List.ofFn rows) (base .output) = base := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, tailBase, oldRoles, hi]
  have final : MachineLazyRows.streamFrame (n := n) (m := m) oldRoles tailBase []
      (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) =
      Function.update (Function.update base .source rest) .output
        (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, MachineLazyRows.recordsInput, tailBase, oldRoles]
  have run := MachineLazyRows.vertexTrace d positive (2 * d) d oldRoles oldRoles_injective
    Label.oldRows (some .nextVertex) (program d positive) (fun _ => rfl)
    tailBase rows cleanBase () (base .output)
  simpa only [initial, final, clean] using run

def prefixSteps (n m : Nat) (rows : List Bool) : Nat :=
  2 * (encodeWords [n, m] ++ rows).length + 5 * n + 3 * m + 17

theorem prefixTrace (d : Nat) (positive : 0 < d) (n m : Nat) (rows : List Bool) :
    (advance (TM2.step (program d positive)))^[prefixSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive,
        initialTapes (encodeWords [n, m] ++ rows)⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d (encodeWords [n, m] ++ rows) n m n 0 rows (encodeWords [n, 2 * m])⟩ := by
  let word := encodeWords [n, m] ++ rows
  let header := encodeWords [n, 2 * m]
  let b₁ := frame word rows [] (encodeWord n) (encodeWord m) [] [] []
  let b₂ := frame word rows (encodeWord (2 * m)) (encodeWord n) (encodeWord m) [] [] []
  let b₃ := frame word rows header (encodeWord n) (encodeWord m) [] [] []
  let b₄ := frame word rows header (encodeWord n) (encodeWord m) (encodeWord n) [] []
  have hstart : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.initialTapes word) (fun _ => []) = initialTapes word := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.initialTapes, MachineTableSplit.tapes, initialTapes, frame]
  have hend : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.resultTapes n m rows) (fun _ => []) = b₁ := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.resultTapes, MachineTableSplit.tapes, b₁, frame, word]
  have split := MachineCloudPadding.Placement.trace splitRoles splitView
    splitRoles_left splitRoles_right Label.split (some .dartSeed) (fun _ => [])
    MachineTableSplit.program (program d positive) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n m rows (clean d positive).1 none)
  have c₀ : (advance (TM2.step (program d positive)))^[MachineTableSplit.exactSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes word⟩) =
      some ⟨some .dartSeed, clean d positive, b₁⟩ := by
    simp only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label] at split
    rw [hstart, hend] at split
    simpa only [clean_pair] using split
  have hdart : Function.update b₁ Tape.output (encodeWord (2 * m + 0) ++ b₁ .output) = b₂ := by
    funext t; cases t <;> simp [b₁, b₂, frame]
  have dart := MachineUnaryAffineAt.seededAffineTrace Tape.darts .scratch .output
    (by decide) (by decide) (by decide) 2 0 .dartSeed .dartScan .dartRestore
    (some .vertexSeed) (program d positive) rfl rfl rfl b₁ m []
    (by simp [b₁, frame]) rfl (clean d positive).1 none
  have c₁ : (advance (TM2.step (program d positive)))^[2 * (m + 1) + 1]
      (some ⟨some .dartSeed, clean d positive, b₁⟩) =
      some ⟨some .vertexSeed, clean d positive, b₂⟩ := by
    simpa only [hdart, clean_pair] using dart
  have hv : Function.update b₂ Tape.output (encodeWord (1 * n + 0) ++ b₂ .output) = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, frame, header, encodeWords]
  have vertex := MachineUnaryAffineAt.seededAffineTrace Tape.vertices .scratch .output
    (by decide) (by decide) (by decide) 1 0 .vertexSeed .vertexScan .vertexRestore
    (some .fuelFirst) (program d positive) rfl rfl rfl b₂ n []
    (by simp [b₂, frame]) rfl (clean d positive).1 none
  have c₂ : (advance (TM2.step (program d positive)))^[2 * (n + 1) + 1]
      (some ⟨some .vertexSeed, clean d positive, b₂⟩) =
      some ⟨some .fuelFirst, clean d positive, b₃⟩ := by
    simpa only [hv, clean_pair] using vertex
  have hf : Function.update b₃ Tape.fuel (b₃ .vertices ++ b₃ .fuel) = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have fuel := MachineCopy.copyTrace Tape.vertices .fuel .scratch
    (by decide) (by decide) (by decide) false .fuelFirst .fuelSecond
    (some .seedCounters) (program d positive) rfl rfl b₃ rfl (clean d positive).1 none
  rw [hf] at fuel
  have c₃ : (advance (TM2.step (program d positive)))^[2 * (n + 2)]
      (some ⟨some .fuelFirst, clean d positive, b₃⟩) =
      some ⟨some .seedCounters, clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .vertices = encodeWord n from rfl, encodeWord_length,
      Nat.add_assoc] using fuel
  have c₄ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .seedCounters, clean d positive, b₄⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d word n m n 0 rows header⟩ := by
    have ht : Function.update (Function.update b₄ Tape.vertex [false]) Tape.reverse [false] =
        loopTapes d word n m n 0 rows header := by
      funext t; cases t <;> simp [b₄, loopTapes, frame, encodeWord]
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄
  have hc : MachineTableSplit.exactSteps n m rows + (2 * (m + 1) + 1) +
      (2 * (n + 1) + 1) + 2 * (n + 2) + 1 = prefixSteps n m rows := by
    dsimp [MachineTableSplit.exactSteps, prefixSteps]
    omega
  rw [hc] at all
  exact all

def vertexBlock {n m : Nat} (d v : Nat) (rows : Fin d → GraphTables.DartRow n m) : List Bool :=
  MachineDummyRows.rowsBits v (2 * d * v) d ++
    MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)

def bodySteps {n m : Nat} (d v : Nat) (rows : Fin d → GraphTables.DartRow n m)
    (output : List Bool) : Nat :=
  2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) + (v + 2) + 8193 +
    MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows)
      (output ++ MachineDummyRows.rowsBits v (2 * d * v) d) + 1

theorem frame_old_empty (input source output vertices darts fuel vertex reverse : List Bool)
    (i : Fin 10) (h7 : i ≠ 7) (h9 : i ≠ 9) :
    frame input source output vertices darts fuel vertex reverse (oldRoles i) = [] := by
  fin_cases i <;> simp_all [frame, oldRoles]

theorem bodyTrace {n m : Nat} (d : Nat) (positive : 0 < d) (input : List Bool)
    (left v : Nat) (rows : Fin d → GraphTables.DartRow n m) (rest output : List Bool) :
    (advance (TM2.step (program d positive)))^[bodySteps d v rows output]
      (some ⟨some .copyVertexFirst, clean d positive,
        loopTapes d input n m left v (MachineLazyRows.recordsInput (List.ofFn rows) ++ rest) output⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
  let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let moving := MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)
  let b₀ := loopTapes d input n m left v source output
  let b₁ := Function.update b₀ Tape.tail (encodeWord v)
  let b₄ := frame input source (output ++ dummy) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  let b₂ := Function.update (Function.update b₄ Tape.tail (encodeWord v))
    Tape.relation MachineDummyRows.trueBits
  let b₃ := Function.update b₄ Tape.relation MachineDummyRows.trueBits
  let b₅ := frame input rest ((output ++ dummy) ++ moving) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  have hcopy : Function.update b₀ Tape.tail (b₀ .vertex ++ b₀ .tail) = b₁ := by
    simp [b₀, b₁, loopTapes, frame]
  have copy := MachineCopy.copyTrace Tape.vertex .tail .scratch
    (by decide) (by decide) (by decide) false .copyVertexFirst .copyVertexSecond
    (some (.dummy (MachineDummyRows.start d))) (program d positive) rfl rfl b₀ rfl
    (clean d positive).1 none
  rw [hcopy] at copy
  have c₀ : (advance (TM2.step (program d positive)))^[2 * (v + 2)]
      (some ⟨some .copyVertexFirst, clean d positive, b₀⟩) =
      some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩ := by
    simpa only [clean_pair, show b₀ .vertex = encodeWord v from rfl, encodeWord_length,
      Nat.add_assoc] using copy
  have hdummy : Function.update (Function.update (Function.update b₁ Tape.reverse
      (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
      Tape.output (b₁ .output ++ dummy) = b₂ := by
    funext t; cases t <;> simp [b₀, b₁, b₂, b₄, loopTapes, frame]
  have dummies := dummyTrace d positive b₁ v (2 * d * v)
    (by simp [b₁]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame])
  have c₁ : (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v
      (2 * d * v) output d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩) =
      some ⟨some .clearDummyTail, clean d positive, b₂⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update b₁ Tape.reverse
          (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
          Tape.output (b₁ .output ++ dummy)⟩ at dummies
    rw [hdummy] at dummies
    simpa only [show b₁ .output = output by simp [b₁, b₀, loopTapes, frame]] using dummies
  have ht : Function.update b₂ Tape.tail [] = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, b₄, frame]
  have drainTail := MachineDrain.drainTrace Tape.tail .clearDummyTail (some .clearDummyRelation)
    (program d positive) rfl b₂ (b₂ .tail) (clean d positive).1 none
  simp only [Function.update_eq_self, ht] at drainTail
  have c₂ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearDummyTail, clean d positive, b₂⟩) =
      some ⟨some .clearDummyRelation, clean d positive, b₃⟩ := by
    simpa only [clean_pair, show b₂ .tail = encodeWord v by simp [b₂], encodeWord_length,
      Nat.add_assoc] using drainTail
  have hr : Function.update b₃ Tape.relation [] = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have drainRelation := MachineDrain.drainTrace Tape.relation .clearDummyRelation
    (some (.oldRows (0, none))) (program d positive) rfl b₃ (b₃ .relation)
    (clean d positive).1 none
  simp only [Function.update_eq_self, hr] at drainRelation
  have c₃ : (advance (TM2.step (program d positive)))^[8193]
      (some ⟨some .clearDummyRelation, clean d positive, b₃⟩) =
      some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .relation = MachineDummyRows.trueBits by simp [b₃],
      MachineDummyRows.trueBits_length] using drainRelation
  have hmoving : Function.update (Function.update b₄ Tape.source rest) Tape.output
      (b₄ .output ++ moving) = b₅ := by
    funext t; cases t <;> simp [b₄, b₅, frame]
  have old := oldTrace d positive b₄ rows rest rfl
    (fun i h7 h9 => frame_old_empty _ _ _ _ _ _ _ _ i h7 h9)
  have c₄ : (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (output ++ dummy)]
      (some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩) =
      some ⟨some .nextVertex, clean d positive, b₅⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update b₄ Tape.source rest) Tape.output
          (b₄ .output ++ moving)⟩ at old
    rw [hmoving] at old
    exact old
  have c₅ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .nextVertex, clean d positive, b₅⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
    have hrev : List.replicate d true ++ encodeWord (2 * d * v + d) =
        encodeWord (2 * d * (v + 1)) := by
      have hw := MachineUnaryAffineAt.prepend_replicate_word d (2 * d * v + d) []
      simp only [List.append_nil] at hw
      rw [hw]
      exact congrArg encodeWord (show d + (2 * d * v + d) = 2 * d * (v + 1) by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have ht : Function.update (Function.update b₅ Tape.reverse
        ((List.replicate d true).reverse ++ b₅ .reverse)) Tape.vertex (true :: b₅ .vertex) =
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows) := by
      funext t
      cases t <;> simp [b₅, frame, loopTapes, vertexBlock, dummy, moving,
        hrev, List.append_assoc]
      simp [encodeWord, List.replicate_succ]
    simp only [Function.iterate_one, advance_some, TM2.step, program,
      stepAux_pushWord, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  exact all

theorem drainPhase (d : Nat) (positive : 0 < d) (tape : Tape) (label : Label d)
    (exit : Option (Label d))
    (atLabel : program d positive label = MachineDrain.drain tape label exit)
    (base : Tape → List Bool) :
    (advance (TM2.step (program d positive)))^[(base tape).length + 1]
      (some ⟨some label, clean d positive, base⟩) =
      some ⟨exit, clean d positive, Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self, clean_pair] using
    MachineDrain.drainTrace tape label exit (program d positive) atLabel base
      (base tape) (clean d positive).1 none

def finishSteps (d n m v : Nat) : Nat := n + m + v + 2 * d * v + 11

theorem finishTrace (d : Nat) (positive : 0 < d) (input output : List Bool) (n m v : Nat) :
    (advance (TM2.step (program d positive)))^[finishSteps d n m v]
      (some ⟨some .guard, clean d positive, loopTapes d input n m 0 v [] output⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
  let b₀ := loopTapes d input n m 0 v [] output
  let b₁ := Function.update b₀ Tape.vertices []
  let b₂ := Function.update b₁ Tape.darts []
  let b₃ := Function.update b₂ Tape.fuel []
  let b₄ := Function.update b₃ Tape.vertex []
  have hframe : MachineUnaryCounter.counterTapes Tape.fuel b₀ 0 [] = b₀ := by
    funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
  have guard := MachineUnaryCounter.guardTrace_zero Tape.fuel .guard .copyVertexFirst
    .clearVertices (program d positive) rfl b₀ [] (clean d positive).1 none
  have c₀ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .guard, clean d positive, b₀⟩) =
      some ⟨some .clearVertices, clean d positive, b₀⟩ := by
    simpa only [hframe, clean_pair] using guard
  have c₁ : (advance (TM2.step (program d positive)))^[n + 2]
      (some ⟨some .clearVertices, clean d positive, b₀⟩) =
      some ⟨some .clearDarts, clean d positive, b₁⟩ := by
    simpa only [show b₀ .vertices = encodeWord n from rfl, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertices .clearVertices (some .clearDarts) rfl b₀
  have c₂ : (advance (TM2.step (program d positive)))^[m + 2]
      (some ⟨some .clearDarts, clean d positive, b₁⟩) =
      some ⟨some .clearFuel, clean d positive, b₂⟩ := by
    have hv : b₁ .darts = encodeWord m := by simp [b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .darts .clearDarts (some .clearFuel) rfl b₁
  have c₃ : (advance (TM2.step (program d positive)))^[2]
      (some ⟨some .clearFuel, clean d positive, b₂⟩) =
      some ⟨some .clearVertex, clean d positive, b₃⟩ := by
    have hv : b₂ .fuel = encodeWord 0 := by simp [b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length] using
      drainPhase d positive .fuel .clearFuel (some .clearVertex) rfl b₂
  have c₄ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearVertex, clean d positive, b₃⟩) =
      some ⟨some .clearReverse, clean d positive, b₄⟩ := by
    have hv : b₃ .vertex = encodeWord v := by simp [b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertex .clearVertex (some .clearReverse) rfl b₃
  have hend : Function.update b₄ Tape.reverse [] = finalTapes input output := by
    funext t; cases t <;> simp [b₄, b₃, b₂, b₁, b₀, loopTapes, finalTapes, frame]
  have c₅ : (advance (TM2.step (program d positive)))^[2 * d * v + 2]
      (some ⟨some .clearReverse, clean d positive, b₄⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
    have hv : b₄ .reverse = encodeWord (2 * d * v) := by
      simp [b₄, b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc, hend] using
      drainPhase d positive .reverse .clearReverse none rfl b₄
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  have hc : 1 + (n + 2) + (m + 2) + 2 + (v + 2) + (2 * d * v + 2) =
      finishSteps d n m v := by dsimp [finishSteps]; omega
  rw [hc] at all
  exact all

def remaining (n r : Nat) : List (Fin n) := (List.finRange n).drop r

@[simp] theorem remaining_zero (n : Nat) : remaining n 0 = List.finRange n := by simp [remaining]
@[simp] theorem remaining_done (n : Nat) : remaining n n = [] := by simp [remaining]

theorem remaining_cons (n r : Nat) (h : r < n) :
    remaining n r = ⟨r, h⟩ :: remaining n (r + 1) := by
  unfold remaining
  rw [List.drop_eq_getElem_cons (l := List.finRange n) (i := r) (by simpa using h)]
  simp

def inputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => MachineLazyRows.recordsInput (List.ofFn (PreprocessingLazyWords.row table v)))

def outputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => vertexBlock d v.val (PreprocessingLazyWords.row table v))

theorem vertexBlock_codec {n d : Nat} (table : PortTables.Table n d) (v : Fin n) :
    vertexBlock d v.val (PreprocessingLazyWords.row table v) =
      encodeWords ((PreprocessingLazyWords.vertexRows table v).flatMap GraphTables.rowWords) := by
  rw [vertexBlock, MachineLazyCodec.rowsBits_stay, MachineLazyRows.recordsOutput_lazy,
    PreprocessingLazyWords.vertexRows, List.flatMap_append, encodeWords_append]

private theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem inputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    inputBlocks table events = encodeWords
      ((events.flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatMap
        GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [inputBlocks, MachineLazyRows.recordsInput_eq_codec]

theorem outputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    outputBlocks table events = encodeWords
      ((events.flatMap (PreprocessingLazyWords.vertexRows table)).flatMap GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [outputBlocks, vertexBlock_codec]

theorem input_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits table = encodeWords [n, n * d] ++ inputBlocks table (List.finRange n) := by
  rw [inputBlocks_codec]
  change encodeWords (PortTables.tableWords table) = _
  rw [PortTables.tableWords_eq, PreprocessingLazyWords.flatRows_list, encodeWords_append]
  have hrows : (List.ofFn (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatten =
      (List.finRange n).flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v)) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hrows]

theorem output_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits (PreprocessingOverlayTables.lazy table) =
      encodeWords [n, 2 * (n * d)] ++ outputBlocks table (List.finRange n) := by
  rw [outputBlocks_codec, PreprocessingLazyWords.tableBits_lazy, encodeWords_append]
  have hm : n * (2 * d) = 2 * (n * d) := by ac_rfl
  have hrows : (List.ofFn (PreprocessingLazyWords.vertexRows table)).flatten =
      (List.finRange n).flatMap (PreprocessingLazyWords.vertexRows table) := by
    rw [List.ofFn_eq_map]
    rfl
  exact congrArg₂ List.append (congrArg (fun k => encodeWords [n, k]) hm)
    (congrArg (fun rows => encodeWords (rows.flatMap GraphTables.rowWords)) hrows)

def loopSteps {n d : Nat} (table : PortTables.Table n d) (r : Nat) : Nat → List Bool → Nat
  | 0, _ => finishSteps d n (n * d) r
  | count + 1, output => if h : r < n then
      (1 + bodySteps d r (PreprocessingLazyWords.row table ⟨r, h⟩) output) +
        loopSteps table (r + 1) count
          (output ++ vertexBlock d r (PreprocessingLazyWords.row table ⟨r, h⟩))
      else 0

theorem loopTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d)
    (input : List Bool) (count r : Nat) (hsum : r + count = n) (output : List Bool) :
    (advance (TM2.step (program d positive)))^[loopSteps table r count output]
      (some ⟨some .guard, clean d positive,
        loopTapes d input n (n * d) count r (inputBlocks table (remaining n r)) output⟩) =
      some ⟨none, clean d positive,
        finalTapes input (output ++ outputBlocks table (remaining n r))⟩ := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    simpa only [loopSteps, remaining_done, inputBlocks, outputBlocks, List.flatMap_nil,
      List.append_nil] using finishTrace d positive input output n (n * d) n
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    let rest := inputBlocks table (remaining n (r + 1))
    let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
    let b₀ := loopTapes d input n (n * d) (count + 1) r source output
    let b₁ := loopTapes d input n (n * d) count r source output
    have hguard (k : Nat) : MachineUnaryCounter.counterTapes Tape.fuel b₀ k [] =
        loopTapes d input n (n * d) k r source output := by
      funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
    have guard := MachineUnaryCounter.guardTrace_succ Tape.fuel .guard .copyVertexFirst
      .clearVertices (program d positive) rfl b₀ count [] (clean d positive).1 none
    have c₀ : (advance (TM2.step (program d positive)))^[1]
        (some ⟨some .guard, clean d positive, b₀⟩) =
        some ⟨some .copyVertexFirst, clean d positive, b₁⟩ := by
      simpa only [hguard, clean_pair] using guard
    have c₁ := bodyTrace d positive input count r rows rest output
    have c₂ := ih (r + 1) (by omega) (output ++ vertexBlock d r rows)
    have all := joinTrace (joinTrace c₀ c₁) c₂
    have hi : inputBlocks table (remaining n r) = source := by
      rw [remaining_cons n r hr]
      rfl
    have ho : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    simpa only [loopSteps, dite_eq_left hr, hi, ho, List.append_assoc] using all

def totalSteps {n d : Nat} (table : PortTables.Table n d) : Nat :=
  prefixSteps n (n * d) (inputBlocks table (List.finRange n)) +
    loopSteps table 0 n (encodeWords [n, 2 * (n * d)])

theorem tableTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    (advance (TM2.step (program d positive)))^[totalSteps table]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes (PortTables.tableBits table)⟩) =
      some ⟨none, clean d positive,
        finalTapes (PortTables.tableBits table)
          (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩ := by
  have prefixRun := prefixTrace d positive n (n * d) (inputBlocks table (List.finRange n))
  rw [← input_table_codec table] at prefixRun
  have loop := loopTrace table positive (PortTables.tableBits table) n 0 (by omega)
    (encodeWords [n, 2 * (n * d)])
  simp only [remaining_zero] at loop
  have all := joinTrace prefixRun loop
  rw [← output_table_codec table] at all
  exact all

private theorem dummyRows_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    have h := ih (e + 1)
    have he : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [he] at h
    nlinarith only [h]

theorem bodySteps_le {n d : Nat} (rows : Fin d → GraphTables.DartRow n (n * d))
    (v L : Nat) (output : List Bool) (hv : v ≤ n) (hn : n ≤ L) (hm : n * d ≤ L)
    (ho : output.length ≤ 20000 * (L + 1) ^ 2) :
    bodySteps d v rows output ≤ 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by
  let D := d + 1
  let N := L + 1
  let P := D * N
  let Q := P * P
  let S := v + 2 * d * v + d + 8194
  let V := (2 * d) * (n * d) + n * d + d
  let R := n + V + 8194
  let C := 2 * n + 8 * (n * d) + V + 4 * R + 8224
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let after := output ++ dummy
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hdD : d ≤ D := by dsimp [D]; omega
  have hLN : L ≤ N := by dsimp [N]; omega
  have hDP : D ≤ P := by
    have h := Nat.mul_le_mul_left D hN
    simpa [P] using h
  have hNP : N ≤ P := by
    have h := Nat.mul_le_mul_right N hD
    simpa [P] using h
  have hP : 1 ≤ P := hN.trans hNP
  have hPQ : P ≤ Q := by
    have h := Nat.mul_le_mul_right P hP
    simpa [Q] using h
  have hQ : 1 ≤ Q := hP.trans hPQ
  have hdP : d ≤ P := hdD.trans hDP
  have hvN : v ≤ N := hv.trans (hn.trans hLN)
  have hvP : v ≤ P := hvN.trans hNP
  have hnP : n ≤ P := hn.trans (hLN.trans hNP)
  have hmN : n * d ≤ N := hm.trans hLN
  have hmP : n * d ≤ P := hmN.trans hNP
  have hdv : d * v ≤ P := by simpa [P] using Nat.mul_le_mul hdD hvN
  have hdm : d * (n * d) ≤ P := by simpa [P] using Nat.mul_le_mul hdD hmN
  have hdPQ : d * P ≤ Q := by simpa [Q] using Nat.mul_le_mul_right P hdP
  have hNQ : N ^ 2 ≤ Q := by simpa [pow_two, Q] using Nat.mul_le_mul hNP hNP
  have hS : S ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [S]
    nlinarith only [hvP, hdP, hdv, hconst, hP]
  have hV : V ≤ 4 * P := by
    dsimp [V]
    nlinarith only [hdm, hmP, hdP]
  have hR : R ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [R]
    nlinarith only [hnP, hV, hconst, hP]
  have hC : C ≤ 50000 * P := by
    have hconst := Nat.mul_le_mul_left 8224 hP
    dsimp [C]
    nlinarith only [hnP, hmP, hV, hR, hconst, hP]
  have hSQ : S ≤ 10000 * Q := hS.trans (Nat.mul_le_mul_left 10000 hPQ)
  have hCQ : C ≤ 50000 * Q := hC.trans (Nat.mul_le_mul_left 50000 hPQ)
  have hdSQ : d * S ≤ 10000 * Q := by
    calc
      d * S ≤ d * (10000 * P) := Nat.mul_le_mul_left d hS
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hdRQ : d * R ≤ 10000 * Q := by
    calc
      d * R ≤ d * (10000 * P) := Nat.mul_le_mul_left d hR
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hOut : output.length ≤ 20000 * Q := by
    change output.length ≤ 20000 * N ^ 2 at ho
    exact ho.trans (Nat.mul_le_mul_left 20000 hNQ)
  have hDummyLength : dummy.length ≤ 10000 * Q := by
    have h := dummyRows_length_le v (2 * d * v) d
    change dummy.length ≤ d * S at h
    exact h.trans hdSQ
  have hAfter : after.length ≤ 30000 * Q := by
    dsimp [after]
    rw [List.length_append]
    omega
  have hDummyInside : 4 * S + 2 * (output.length + d * S) + 10 ≤ 100010 * Q := by
    have hconst := Nat.mul_le_mul_left 10 hQ
    nlinarith only [hSQ, hOut, hdSQ, hconst]
  have hDummySteps : MachineDummyRows.steps v (2 * d * v) output d ≤ 100010 * d * Q := by
    calc
      MachineDummyRows.steps v (2 * d * v) output d ≤
          d * (4 * S + 2 * (output.length + d * S) + 10) := by
        simpa only [S] using MachineDummyRows.steps_le_bound v (2 * d * v) output d
      _ ≤ d * (100010 * Q) := Nat.mul_le_mul_left d hDummyInside
      _ = 100010 * d * Q := by ring
  have hOldInside : C + 2 * (after.length + d * R) + 1 ≤ 130001 * Q := by
    nlinarith only [hCQ, hAfter, hdRQ, hQ]
  have hOldSteps : MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      130001 * d * Q + 1 := by
    have h := MachineLazyRows.vertexSteps_le d (2 * d) d (List.ofFn rows) after
    simp only [List.length_ofFn] at h
    change MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      d * (C + 2 * (after.length + d * R) + 1) + 1 at h
    calc
      MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
          d * (C + 2 * (after.length + d * R) + 1) + 1 := h
      _ ≤ d * (130001 * Q) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left d hOldInside) 1
      _ = 130001 * d * Q + 1 := by ring
  have hvQ : v ≤ Q := hvP.trans hPQ
  have hOverhead : 3 * v + 8201 ≤ 10000 * Q := by
    have hconst := Nat.mul_le_mul_left 8201 hQ
    nlinarith only [hvQ, hconst, hQ]
  have hBody : bodySteps d v rows output ≤ 230011 * d * Q + 10000 * Q + 1 := by
    change 2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) +
      (v + 2) + 8193 + MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after + 1 ≤ _
    nlinarith only [hDummySteps, hOldSteps, hOverhead]
  have hdQQ : d * Q ≤ D * Q := Nat.mul_le_mul_right Q hdD
  have hQQ : Q ≤ D * Q := by simpa using Nat.mul_le_mul_right Q hD
  have hDQ : 1 ≤ D * Q := hQ.trans hQQ
  have hCoarse : bodySteps d v rows output ≤ 300000 * D * Q := by
    nlinarith only [hBody, hdQQ, hQQ, hDQ]
  calc
    bodySteps d v rows output ≤ 300000 * D * Q := hCoarse
    _ ≤ 1000000 * D * Q := by
      have h := Nat.mul_le_mul_right (D * Q) (by norm_num : (300000 : Nat) ≤ 1000000)
      simpa only [Nat.mul_assoc] using h
    _ = 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by dsimp [D, N, P, Q]; ring

theorem output_length_le {n d : Nat} (table : PortTables.Table n d) :
    (PortTables.tableBits (PreprocessingOverlayTables.lazy table)).length ≤
      20000 * ((PortTables.tableBits table).length + 1) ^ 2 := by
  let L := (PortTables.tableBits table).length
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have h := GraphTables.tableBits_length_le
    (PortTables.graphTable (PreprocessingOverlayTables.lazy table))
  change (PortTables.tableBits (PreprocessingOverlayTables.lazy table)).length ≤
    n + n * (2 * d) + 2 + n * (2 * d) * (n + n * (2 * d) + 8192) at h
  have hdouble : n * (2 * d) = 2 * (n * d) := by ac_rfl
  rw [hdouble] at h
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm)
    (Nat.add_le_add_right (Nat.add_le_add hn (Nat.mul_le_mul_left 2 hm)) 8192)
  change _ ≤ 20000 * (L + 1) ^ 2
  nlinarith only [h, hn, hm, hmul]

theorem loopSteps_le {n d : Nat} (table : PortTables.Table n d) (L count r : Nat)
    (hsum : r + count = n) (hn : n ≤ L) (hm : n * d ≤ L) (output : List Bool)
    (hout : (output ++ outputBlocks table (remaining n r)).length ≤ 20000 * (L + 1) ^ 2) :
    loopSteps table r count output ≤
      count * (1 + 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2) + 5 * L + 11 := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    have hdouble : 2 * d * n = 2 * (n * d) := by ac_rfl
    simp only [loopSteps, finishSteps, Nat.zero_mul, Nat.zero_add, hdouble]
    omega
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    have ho : output.length ≤ 20000 * (L + 1) ^ 2 := by
      rw [List.length_append] at hout
      omega
    have hb := bodySteps_le rows r L output hr.le hn hm ho
    have hs : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    have hout' : ((output ++ vertexBlock d r rows) ++
        outputBlocks table (remaining n (r + 1))).length ≤ 20000 * (L + 1) ^ 2 := by
      simpa only [hs, List.append_assoc] using hout
    have ht := ih (r + 1) (by omega) (output ++ vertexBlock d r rows) hout'
    simp only [loopSteps, dite_eq_left hr]
    change (1 + bodySteps d r rows output) +
      loopSteps table (r + 1) count (output ++ vertexBlock d r rows) ≤ _
    nlinarith only [hb, ht]

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (1000000 * (d + 1) ^ 3 + 100) * (Polynomial.X + 1) ^ 3

@[simp] theorem timePolynomial_eval (d L : Nat) :
    (timePolynomial d).eval L = (1000000 * (d + 1) ^ 3 + 100) * (L + 1) ^ 3 := by
  simp [timePolynomial]

theorem totalSteps_le {n d : Nat} (table : PortTables.Table n d) :
    totalSteps table ≤ (timePolynomial d).eval (PortTables.tableBits table).length := by
  let L := (PortTables.tableBits table).length
  let N := L + 1
  let C := 1000000 * (d + 1) ^ 3
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have hout : (encodeWords [n, 2 * (n * d)] ++
      outputBlocks table (remaining n 0)).length ≤ 20000 * (L + 1) ^ 2 := by
    rw [remaining_zero, ← output_table_codec]
    exact output_length_le table
  have hl := loopSteps_le table L n 0 (by omega) hn hm _ hout
  have hp : prefixSteps n (n * d) (inputBlocks table (List.finRange n)) ≤ 10 * L + 17 := by
    unfold prefixSteps
    rw [← input_table_codec table]
    change 2 * L + 5 * n + 3 * (n * d) + 17 ≤ _
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnN : n ≤ N := by dsimp [N]; omega
  have hN2 : 1 ≤ N ^ 2 := by nlinarith only [hN]
  have hN3 : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N hN2
    nlinarith only [h]
  have hc := Nat.mul_le_mul_right (1 + C * N ^ 2) hnN
  change loopSteps table 0 n (encodeWords [n, 2 * (n * d)]) ≤ n * (1 + C * N ^ 2) + 5 * L + 11 at hl
  rw [timePolynomial_eval]
  change totalSteps table ≤ (C + 100) * N ^ 3
  unfold totalSteps
  have hLN : L + 1 = N := rfl
  nlinarith only [hp, hl, hc, hN, hN3, hLN]

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label d
  main := .split .copyFirst
  σ := State d
  initialState := clean d positive
  m := program d positive

theorem machine_alphabet_finite (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((machine d positive).Γ k) := by
  intro k
  change Finite Bool
  infer_instance

theorem initial_configuration (d : Nat) (positive : 0 < d) (input : List Bool) :
    initList (machine d positive) input =
      ⟨some (.split .copyFirst), clean d positive, initialTapes input⟩ := by
  have ht : (initList (machine d positive) input).stk = initialTapes input := by
    funext t; (cases t <;> simp [initList, machine, initialTapes, frame]); rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

@[simp] theorem finalTapes_input (input output : List Bool) : finalTapes input output .input = input := rfl
@[simp] theorem finalTapes_output (input output : List Bool) : finalTapes input output .output = output := rfl

theorem finalTapes_work_empty (input output : List Bool) (t : Tape)
    (hi : t ≠ .input) (ho : t ≠ .output) : finalTapes input output t = [] := by
  cases t <;> simp_all [finalTapes, frame]

def machineInTime {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    StateTransition.EvalsToInTime (machine d positive).step
      (initList (machine d positive) (PortTables.tableBits table))
      (some ⟨none, clean d positive, finalTapes (PortTables.tableBits table)
        (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩)
      ((timePolynomial d).eval (PortTables.tableBits table).length) where
  steps := totalSteps table
  evals_in_steps := by
    rw [initial_configuration]
    exact tableTrace table positive
  steps_le_m := totalSteps_le table

end BinPackingGames.Foundations.Complexity.MachineLazyTable

namespace BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem sourceMachine_eq (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.sourceMachine (rawProgram d positive) =
      MachineLazyTable.machine d positive := rfl

def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime

end OAI
