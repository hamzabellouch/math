import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.Machines.MachineControlEmbedding
import OAI.Computability.BinPacking.Machines.PackingPoolMachine
import OAI.Computability.BinPacking.Machines.PackingPowerProgram

namespace OAI

namespace BinPackingGap.GraphFieldMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open GraphTallyMachine (Mode Slot afterName initial transition)

inductive Field
  | threshold
  | endpoints
  deriving DecidableEq

instance : Fintype Field where
  elems := {.threshold, .endpoints}
  complete field := by cases field <;> simp

def keepsName : Field → Slot → Bool
  | .threshold, .header => true
  | .endpoints, .edgeFirst => true
  | .endpoints, .edgeSecond => true
  | _, _ => false

def emit : Field → Mode → Bool → List Bool
  | .threshold, .name .header, bit => [bit]
  | .threshold, .digit .header, bit => [bit]
  | .endpoints, .endpoints, bit => [bit]
  | .endpoints, .name .edgeFirst, bit => [bit]
  | .endpoints, .digit .edgeFirst, bit => [bit]
  | .endpoints, .name .edgeSecond, bit => [bit]
  | .endpoints, .digit .edgeSecond, bit => [bit]
  | _, _, _ => []

def scanOutput (field : Field) : Mode → List Bool → List Bool :=
  MachineTransducer.output transition (emit field)

@[simp] theorem scanOutput_nil (field : Field) (mode : Mode) :
    scanOutput field mode [] = [] := rfl

theorem scanOutput_cons (field : Field) (mode : Mode) (bit : Bool) (rest : List Bool) :
    scanOutput field mode (bit :: rest) =
      emit field mode bit ++ scanOutput field (transition mode bit) rest := rfl

theorem scanOutput_done (field : Field) (input : List Bool) :
    scanOutput field .done input = [] := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
      cases field <;> simp only [scanOutput_cons, transition, emit, List.nil_append, ih]

theorem scanOutput_frame (field : Field) (slot : Slot) (bits suffix : List Bool) :
    scanOutput field (.name slot)
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      (if keepsName field slot then BinPackingCompleteness.BinaryEncoding.frame bits else []) ++
        scanOutput field (afterName slot) suffix := by
  induction bits with
  | nil => cases field <;> cases slot <;> rfl
  | cons bit bits ih =>
      cases field <;> cases slot <;>
        simp [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
          scanOutput_cons, transition, emit, keepsName, afterName, ih]

theorem scanOutput_natBits (field : Field) (slot : Slot) (n : Nat) (suffix : List Bool) :
    scanOutput field (.name slot) (natBits n ++ suffix) =
      (if keepsName field slot then natBits n else []) ++
        scanOutput field (afterName slot) suffix :=
  scanOutput_frame field slot n.bits suffix

theorem scanOutput_pairBits (field : Field) (edge : Nat × Nat) (suffix : List Bool) :
    scanOutput field (.name .edgeFirst) (pairBits natBits natBits edge ++ suffix) =
      (if field = .endpoints then pairBits natBits natBits edge else []) ++
        scanOutput field .endpoints suffix := by
  cases field <;>
    simp [pairBits, List.append_assoc, scanOutput_natBits, keepsName, afterName]

theorem scanOutput_vertices (field : Field) (vertices : List Nat) (suffix : List Bool) :
    scanOutput field .vertices (listBits natBits vertices ++ suffix) =
      scanOutput field .endpoints suffix := by
  induction vertices with
  | nil => cases field <;> rfl
  | cons vertex vertices ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_natBits, keepsName, afterName, ih]

theorem scanOutput_endpoints (field : Field) (endpoints : List (Nat × Nat))
    (suffix : List Bool) :
    scanOutput field .endpoints (listBits (pairBits natBits natBits) endpoints ++ suffix) =
      (if field = .endpoints then listBits (pairBits natBits natBits) endpoints else []) ++
        scanOutput field .done suffix := by
  induction endpoints with
  | nil => cases field <;> rfl
  | cons edge endpoints ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_pairBits, ih]

def fieldsOutput : Field → GraphFields → List Bool
  | .threshold, fields => natBits fields.k
  | .endpoints, fields => listBits (pairBits natBits natBits) fields.endpoints

def fieldBits (field : Field) (input : GraphReductionInput) : List Bool :=
  fieldsOutput field input.fields

@[simp] theorem thresholdBits (input : GraphReductionInput) :
    fieldBits .threshold input = natBits input.k := rfl

@[simp] theorem endpointsBits (input : GraphReductionInput) :
    fieldBits .endpoints input =
      listBits (pairBits natBits natBits) input.graph.endpointPairs := rfl

theorem output_graphFields (field : Field) (fields : GraphFields) :
    scanOutput field initial fields.bits = fieldsOutput field fields := by
  have hend := scanOutput_endpoints field fields.endpoints []
  simp only [List.append_nil, scanOutput_nil] at hend
  cases field <;>
    simp [GraphFields.bits, List.append_assoc, initial, scanOutput_natBits,
      keepsName, afterName, scanOutput_vertices, fieldsOutput, hend]

theorem output_graphBits (field : Field) (input : GraphReductionInput) :
    scanOutput field initial (graphBits input) = fieldBits field input :=
  output_graphFields field input.fields

theorem emit_length_le (field : Field) (mode : Mode) (bit : Bool) :
    (emit field mode bit).length ≤ 1 := by
  cases mode with
  | vertices => cases field <;> simp [emit]
  | endpoints => cases field <;> simp [emit]
  | name slot => cases field <;> cases slot <;> simp [emit]
  | digit slot => cases field <;> cases slot <;> simp [emit]
  | done => cases field <;> simp [emit]

theorem scanOutput_length_le (field : Field) (mode : Mode) (input : List Bool) :
    (scanOutput field mode input).length ≤ input.length := by
  induction input generalizing mode with
  | nil => exact Nat.le_refl _
  | cons bit input ih =>
      rw [scanOutput_cons, List.length_append, List.length_cons]
      have he := emit_length_le field mode bit
      have hi := ih (transition mode bit)
      omega

theorem fieldBits_length_le (field : Field) (input : GraphReductionInput) :
    (fieldBits field input).length ≤ (graphBits input).length := by
  rw [← output_graphBits]
  exact scanOutput_length_le field initial (graphBits input)

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := MachineTransducerCopy.State σ Mode

def clean (ambient : σ) : State σ := ((ambient, initial), none)

def fieldCopyInTime (field : Field) (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (scanLabel restoreLabel : Λ) (emitterLabel : Mode → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atScan : program scanLabel =
      MachineTransducerCopy.scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      MachineTransducerCopy.emitter destination transition (emit field) scanLabel control symbol)
    (atRestore : program restoreLabel =
      MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (input : GraphReductionInput) (sourceWord : base source = graphBits input)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, ((ambient, initial), register), base⟩
      (some ⟨exit, clean ambient, Function.update base destination
        ((fieldBits field input).reverse ++ base destination)⟩)
      (3 * (graphBits input).length + 2) := by
  have run := MachineTransducerCopy.transduceCopyInTime source scratch destination
    sourceScratch sourceDestination scratchDestination initial transition (emit field)
    scanLabel restoreLabel emitterLabel exit program atScan atEmitter atRestore
    base scratchEmpty ambient initial register
  have hout : MachineTransducer.output transition (emit field) initial (base source) =
      fieldBits field input := by
    change scanOutput field initial (base source) = _
    rw [sourceWord, output_graphBits]
  rw [hout] at run
  simpa only [sourceWord, clean] using run

inductive Label
  | scan | restore | transfer
  | emitter (mode : Mode) (bit : Bool)
  deriving DecidableEq, Fintype

def instruction (field : Field) (slots : Fin 4 ↪ K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) initial
      (fun mode bit => labels (.emitter mode bit)) (labels .restore)
  | .emitter mode bit => MachineTransducerCopy.emitter (slots 2) transition (emit field)
      (labels .scan) mode bit
  | .restore => MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) (some (labels .transfer))
  | .transfer => MachineTransfer.loopAt (slots 2) (slots 3) id false
      (labels .transfer) exit

def resultTapes (field : Field) (slots : Fin 4 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) : K → List Bool :=
  Function.update base (slots 3) (fieldBits field input ++ base (slots 3))

def steps (field : Field) (input : GraphReductionInput) : Nat :=
  (3 * (graphBits input).length + 2) + ((fieldBits field input).length + 1)

theorem steps_le (field : Field) (input : GraphReductionInput) :
    steps field input ≤ 4 * (graphBits input).length + 3 := by
  have h := fieldBits_length_le field input
  unfold steps
  omega

theorem extractTrace (field : Field) (slots : Fin 4 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input)
    (scratchEmpty : base (slots 1) = []) (temporaryEmpty : base (slots 2) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[steps field input]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes field slots base input⟩ := by
  have hd (i j : Fin 4) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let middle := Function.update base (slots 2) (fieldBits field input).reverse
  have first : (MachineComposition.advance (TM2.step program))^[3 * (graphBits input).length + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨some (labels .transfer), clean ambient, middle⟩ := by
    have run := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
      initial transition (emit field) (labels .scan) (labels .restore)
      (fun mode bit => labels (.emitter mode bit)) (some (labels .transfer))
      program (atLabels .scan) (fun mode bit => atLabels (.emitter mode bit))
      (atLabels .restore) base scratchEmpty ambient initial none
    have hout : MachineTransducer.output transition (emit field) initial (base (slots 0)) =
        fieldBits field input := by
      change scanOutput field initial (base (slots 0)) = _
      rw [sourceWord, output_graphBits]
    rw [hout] at run
    simpa only [sourceWord, temporaryEmpty, List.append_nil, clean, middle] using run
  have middleSource : middle (slots 2) = (fieldBits field input).reverse := by simp [middle]
  have middleDestination : middle (slots 3) = base (slots 3) := by
    simp [middle, hd 3 2 (by decide)]
  have finalTapes : MachineTransfer.tapesAt (slots 2) (slots 3) middle []
      (fieldBits field input ++ base (slots 3)) = resultTapes field slots base input := by
    funext k
    by_cases ht : k = slots 2
    · subst k
      simp [MachineTransfer.tapesAt, resultTapes, temporaryEmpty, hd 2 3 (by decide)]
    · by_cases ho : k = slots 3
      · subst k
        simp [MachineTransfer.tapesAt, resultTapes]
      · simp [MachineTransfer.tapesAt, resultTapes, middle, ht, ho]
  have second : (MachineComposition.advance (TM2.step program))^[(fieldBits field input).length + 1]
      (some ⟨some (labels .transfer), clean ambient, middle⟩) =
      some ⟨exit, clean ambient, resultTapes field slots base input⟩ := by
    have run := MachineTransfer.transferAt_fromTapes
      (Γ := MachineTransducerCopy.Alphabet K) (σ := σ × Mode) (slots 2) (slots 3)
      (hd 2 3 (by decide)) id false (labels .transfer) exit program
      (by simpa only [instruction] using atLabels .transfer) middle (ambient, initial) none
    have next_eq : MachineTransfer.nextAt (slots 3) program =
        MachineComposition.advance (TM2.step program) := by
      funext configuration
      rfl
    rw [next_eq, middleSource, middleDestination] at run
    simpa only [List.length_reverse, List.reverse_reverse, List.map_id,
      finalTapes, clean] using run
  rw [steps, Nat.add_comm, Function.iterate_add_apply, first, second]

def extractInTime (field : Field) (slots : Fin 4 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input)
    (scratchEmpty : base (slots 1) = []) (temporaryEmpty : base (slots 2) = [])
    (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes field slots base input⟩)
      (4 * (graphBits input).length + 3) where
  steps := steps field input
  evals_in_steps := extractTrace field slots labels exit program atLabels base input
    sourceWord scratchEmpty temporaryEmpty ambient
  steps_le_m := steps_le field input

end BinPackingGap.GraphFieldMachine

namespace BinPackingGap.GraphTokenMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open GraphTallyMachine (Mode Slot afterName initial transition)

inductive Field
  | vertex
  | edge
  deriving DecidableEq

instance : Fintype Field where
  elems := {.vertex, .edge}
  complete field := by cases field <;> simp

def emit : Field → Mode → Bool → List Bool
  | .vertex, .vertices, true => [true]
  | .edge, .endpoints, true => [true]
  | _, _, _ => []

def scanOutput (field : Field) : Mode → List Bool → List Bool :=
  MachineTransducer.output transition (emit field)

@[simp] theorem scanOutput_nil (field : Field) (mode : Mode) :
    scanOutput field mode [] = [] := rfl

theorem scanOutput_cons (field : Field) (mode : Mode) (bit : Bool) (rest : List Bool) :
    scanOutput field mode (bit :: rest) =
      emit field mode bit ++ scanOutput field (transition mode bit) rest := rfl

theorem scanOutput_done (field : Field) (input : List Bool) :
    scanOutput field .done input = [] := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
      cases field <;> simp only [scanOutput_cons, transition, emit, List.nil_append, ih]

theorem scanOutput_frame (field : Field) (slot : Slot) (bits suffix : List Bool) :
    scanOutput field (.name slot)
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      scanOutput field (afterName slot) suffix := by
  induction bits with
  | nil => cases field <;> rfl
  | cons bit bits ih =>
      cases field <;>
        simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
          scanOutput_cons, transition, emit, List.nil_append] using ih

theorem scanOutput_natBits (field : Field) (slot : Slot) (n : Nat) (suffix : List Bool) :
    scanOutput field (.name slot) (natBits n ++ suffix) =
      scanOutput field (afterName slot) suffix :=
  scanOutput_frame field slot n.bits suffix

theorem scanOutput_pairBits (field : Field) (edge : Nat × Nat) (suffix : List Bool) :
    scanOutput field (.name .edgeFirst) (pairBits natBits natBits edge ++ suffix) =
      scanOutput field .endpoints suffix := by
  simp only [pairBits, List.append_assoc, scanOutput_natBits, afterName]

theorem scanOutput_vertices (field : Field) (vertices : List Nat) (suffix : List Bool) :
    scanOutput field .vertices (listBits natBits vertices ++ suffix) =
      (if field = .vertex then List.replicate vertices.length true else []) ++
        scanOutput field .endpoints suffix := by
  induction vertices with
  | nil => cases field <;> rfl
  | cons vertex vertices ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_natBits, afterName, ih, List.replicate_succ]

theorem scanOutput_endpoints (field : Field) (endpoints : List (Nat × Nat))
    (suffix : List Bool) :
    scanOutput field .endpoints (listBits (pairBits natBits natBits) endpoints ++ suffix) =
      (if field = .edge then List.replicate endpoints.length true else []) ++
        scanOutput field .done suffix := by
  induction endpoints with
  | nil => cases field <;> rfl
  | cons edge endpoints ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_pairBits, ih, List.replicate_succ]

def fieldsCount : Field → GraphFields → Nat
  | .vertex, fields => fields.vertices.length
  | .edge, fields => fields.endpoints.length

def count : Field → GraphReductionInput → Nat
  | .vertex, input => input.graph.n
  | .edge, input => input.graph.edges.length

def tokenBits (field : Field) (input : GraphReductionInput) : List Bool :=
  List.replicate (count field input) true

@[simp] theorem count_vertex (input : GraphReductionInput) :
    count .vertex input = input.graph.n := rfl

@[simp] theorem count_edge (input : GraphReductionInput) :
    count .edge input = input.graph.edges.length := rfl

@[simp] theorem tokenBits_length (field : Field) (input : GraphReductionInput) :
    (tokenBits field input).length = count field input := by simp [tokenBits]

@[simp] theorem tokenBits_reverse (field : Field) (input : GraphReductionInput) :
    (tokenBits field input).reverse = tokenBits field input := by simp [tokenBits]

theorem output_graphFields (field : Field) (fields : GraphFields) :
    scanOutput field initial fields.bits = List.replicate (fieldsCount field fields) true := by
  have hend := scanOutput_endpoints field fields.endpoints []
  simp only [List.append_nil, scanOutput_nil] at hend
  cases field <;>
    simp [GraphFields.bits, List.append_assoc, initial, scanOutput_natBits,
      afterName, scanOutput_vertices, fieldsCount, hend]

theorem fieldsCount_fields (field : Field) (input : GraphReductionInput) :
    fieldsCount field input.fields = count field input := by
  cases field <;> simp [fieldsCount, count, GraphReductionInput.fields]

theorem output_graphBits (field : Field) (input : GraphReductionInput) :
    scanOutput field initial (graphBits input) = tokenBits field input := by
  simpa only [graphBits, fieldsCount_fields, tokenBits] using
    output_graphFields field input.fields

theorem count_le_bits (field : Field) (input : GraphReductionInput) :
    count field input ≤ (graphBits input).length := by
  cases field with
  | vertex => exact graph_vertexCount_le_bits input
  | edge => exact graph_edgeCount_le_bits input

theorem emit_length_le (field : Field) (mode : Mode) (bit : Bool) :
    (emit field mode bit).length ≤ 1 := by
  cases field <;> cases mode <;> cases bit <;> simp [emit]

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := MachineTransducerCopy.State σ Mode

def clean (ambient : σ) : State σ := ((ambient, initial), none)

inductive Label
  | scan
  | restore
  | emitter (mode : Mode) (bit : Bool)
  deriving DecidableEq, Fintype

def instruction (field : Field) (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) initial
      (fun mode bit => labels (.emitter mode bit)) (labels .restore)
  | .emitter mode bit => MachineTransducerCopy.emitter (slots 2) transition (emit field)
      (labels .scan) mode bit
  | .restore => MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) exit

def resultTapes (field : Field) (slots : Fin 3 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) : K → List Bool :=
  Function.update base (slots 2) (tokenBits field input ++ base (slots 2))

theorem resultTapes_other (field : Field) (slots : Fin 3 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) (k : K) (hne : k ≠ slots 2) :
    resultTapes field slots base input k = base k := by simp [resultTapes, hne]

@[simp] theorem resultTapes_destination (field : Field) (slots : Fin 3 ↪ K)
    (base : K → List Bool) (input : GraphReductionInput) :
    resultTapes field slots base input (slots 2) = tokenBits field input ++ base (slots 2) := by
  simp [resultTapes]

theorem tokensTrace (field : Field) (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input) (scratchEmpty : base (slots 1) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[3 * (graphBits input).length + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes field slots base input⟩ := by
  have hd (i j : Fin 3) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  have run := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
    initial transition (emit field) (labels .scan) (labels .restore)
    (fun mode bit => labels (.emitter mode bit)) exit program
    (atLabels .scan) (fun mode bit => atLabels (.emitter mode bit))
    (atLabels .restore) base scratchEmpty ambient initial none
  have hout : MachineTransducer.output transition (emit field) initial (base (slots 0)) =
      tokenBits field input := by
    change scanOutput field initial (base (slots 0)) = _
    rw [sourceWord, output_graphBits]
  rw [hout] at run
  simpa only [sourceWord, tokenBits_reverse, clean, resultTapes] using run

def tokensInTime (field : Field) (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input) (scratchEmpty : base (slots 1) = [])
    (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes field slots base input⟩)
      (3 * (graphBits input).length + 2) where
  steps := 3 * (graphBits input).length + 2
  evals_in_steps := tokensTrace field slots labels exit program atLabels base input
    sourceWord scratchEmpty ambient
  steps_le_m := Nat.le_refl _

theorem resultTapes_counter (field : Field) (slots : Fin 3 ↪ K)
    (base : K → List Bool) (input : GraphReductionInput)
    (destinationTerminated : base (slots 2) = [false]) :
    resultTapes field slots base input =
      Function.update base (slots 2) (encodeWord (count field input)) := by
  simp only [resultTapes, destinationTerminated, tokenBits, encodeWord]

def counterInTime (field : Field) (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input) (scratchEmpty : base (slots 1) = [])
    (destinationTerminated : base (slots 2) = [false]) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (slots 2) (encodeWord (count field input))⟩)
      (3 * (graphBits input).length + 2) := by
  have run := tokensInTime field slots labels exit program atLabels base input
    sourceWord scratchEmpty ambient
  rw [resultTapes_counter field slots base input destinationTerminated] at run
  exact run

end BinPackingGap.GraphTokenMachine

namespace BinPackingGap.GraphPreparationMachine

open Turing
open BinPackingGames.Foundations.Complexity

abbrev State (A : Type) := GraphFieldMachine.State A

inductive Label
  | threshold (label : GraphFieldMachine.Label)
  | endpoints (label : GraphFieldMachine.Label)
  | vertices (label : GraphTokenMachine.Label)
  | edges (label : GraphTokenMachine.Label)
  deriving DecidableEq, Fintype

def fieldIndices (edge : Bool) : Fin 4 ↪ Fin 7 where
  toFun := if edge then ![0, 1, 2, 4] else ![0, 1, 2, 3]
  inj' := by cases edge <;> decide

def tokenIndices (edge : Bool) : Fin 3 ↪ Fin 7 where
  toFun := if edge then ![0, 1, 6] else ![0, 1, 5]
  inj' := by cases edge <;> decide

variable {K Λ A : Type} [DecidableEq K]

def fieldSlots (slots : Fin 7 ↪ K) (edge : Bool) : Fin 4 ↪ K :=
  (fieldIndices edge).trans slots

def tokenSlots (slots : Fin 7 ↪ K) (edge : Bool) : Fin 3 ↪ K :=
  (tokenIndices edge).trans slots

omit [DecidableEq K] in
@[simp] theorem fieldSlots_zero [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 0 = slots 0 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem fieldSlots_one [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 1 = slots 1 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem fieldSlots_two [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 2 = slots 2 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem fieldSlots_three [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 3 = slots (if edge then 4 else 3) := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem tokenSlots_zero [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    tokenSlots slots edge 0 = slots 0 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem tokenSlots_one [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    tokenSlots slots edge 1 = slots 1 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem tokenSlots_two [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    tokenSlots slots edge 2 = slots (if edge then 6 else 5) := by cases edge <;> rfl

def instruction (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .threshold l => GraphFieldMachine.instruction .threshold (fieldSlots slots false)
      (fun l => labels (.threshold l)) (some (labels (.endpoints .scan))) l
  | .endpoints l => GraphFieldMachine.instruction .endpoints (fieldSlots slots true)
      (fun l => labels (.endpoints l)) (some (labels (.vertices .scan))) l
  | .vertices l => GraphTokenMachine.instruction .vertex (tokenSlots slots false)
      (fun l => labels (.vertices l)) (some (labels (.edges .scan))) l
  | .edges l => GraphTokenMachine.instruction .edge (tokenSlots slots true)
      (fun l => labels (.edges l)) exit l

def preparedTapes (slots : Fin 7 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) : K → List Bool :=
  GraphTokenMachine.resultTapes .edge (tokenSlots slots true)
    (GraphTokenMachine.resultTapes .vertex (tokenSlots slots false)
      (GraphFieldMachine.resultTapes .endpoints (fieldSlots slots true)
        (GraphFieldMachine.resultTapes .threshold (fieldSlots slots false) base input)
        input) input) input

def steps (input : GraphReductionInput) : Nat :=
  GraphFieldMachine.steps .threshold input + GraphFieldMachine.steps .endpoints input +
    (3 * (graphBits input).length + 2) + (3 * (graphBits input).length + 2)

theorem preparedTapes_register (slots : Fin 7 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) (j : Fin 7) :
    preparedTapes slots base input (slots j) =
      match j.val with
      | 3 => GraphFieldMachine.fieldBits .threshold input ++ base (slots 3)
      | 4 => GraphFieldMachine.fieldBits .endpoints input ++ base (slots 4)
      | 5 => List.replicate input.graph.n true ++ base (slots 5)
      | 6 => List.replicate input.graph.edges.length true ++ base (slots 6)
      | _ => base (slots j) := by
  fin_cases j <;>
    simp [preparedTapes, GraphFieldMachine.resultTapes, GraphTokenMachine.resultTapes,
      GraphTokenMachine.tokenBits, GraphTokenMachine.count, slots.injective.eq_iff]

theorem preparedTapes_other (slots : Fin 7 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) (k : K)
    (h₃ : k ≠ slots 3) (h₄ : k ≠ slots 4) (h₅ : k ≠ slots 5) (h₆ : k ≠ slots 6) :
    preparedTapes slots base input k = base k := by
  simp [preparedTapes, GraphFieldMachine.resultTapes, GraphTokenMachine.resultTapes,
    h₃, h₄, h₅, h₆]

theorem steps_le (input : GraphReductionInput) :
    steps input ≤ 14 * (graphBits input).length + 10 := by
  have hk := GraphFieldMachine.steps_le .threshold input
  have he := GraphFieldMachine.steps_le .endpoints input
  unfold steps
  omega

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem preparationTrace (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, P (labels l) = instruction slots labels exit l)
    (base : K → List Bool) (input : GraphReductionInput)
    (graphWord : base (slots 0) = graphBits input)
    (scratchEmpty : base (slots 1) = []) (temporaryEmpty : base (slots 2) = [])
    (ambient : A) :
    (MachineComposition.advance (TM2.step P))^[steps input]
      (some ⟨some (labels (.threshold .scan)), GraphFieldMachine.clean ambient, base⟩) =
      some ⟨exit, GraphFieldMachine.clean ambient, preparedTapes slots base input⟩ := by
  have hd (i j : Fin 7) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  let b₁ := GraphFieldMachine.resultTapes .threshold (fieldSlots slots false) base input
  let b₂ := GraphFieldMachine.resultTapes .endpoints (fieldSlots slots true) b₁ input
  let b₃ := GraphTokenMachine.resultTapes .vertex (tokenSlots slots false) b₂ input
  have g₁ : b₁ (slots 0) = graphBits input := by
    simp [b₁, GraphFieldMachine.resultTapes, hd 0 3 (by decide), graphWord]
  have s₁ : b₁ (slots 1) = [] := by
    simp [b₁, GraphFieldMachine.resultTapes, hd 1 3 (by decide), scratchEmpty]
  have t₁ : b₁ (slots 2) = [] := by
    simp [b₁, GraphFieldMachine.resultTapes, hd 2 3 (by decide), temporaryEmpty]
  have g₂ : b₂ (slots 0) = graphBits input := by
    simp [b₂, GraphFieldMachine.resultTapes, hd 0 4 (by decide), g₁]
  have s₂ : b₂ (slots 1) = [] := by
    simp [b₂, GraphFieldMachine.resultTapes, hd 1 4 (by decide), s₁]
  have g₃ : b₃ (slots 0) = graphBits input := by
    simp [b₃, GraphTokenMachine.resultTapes, hd 0 5 (by decide), g₂]
  have s₃ : b₃ (slots 1) = [] := by
    simp [b₃, GraphTokenMachine.resultTapes, hd 1 5 (by decide), s₂]
  have r₁ := GraphFieldMachine.extractTrace .threshold (fieldSlots slots false)
    (fun l => labels (.threshold l)) (some (labels (.endpoints .scan))) P
    (fun l => atLabels (.threshold l)) base input
    (by simpa using graphWord) (by simpa using scratchEmpty)
    (by simpa using temporaryEmpty) ambient
  have r₂ := GraphFieldMachine.extractTrace .endpoints (fieldSlots slots true)
    (fun l => labels (.endpoints l)) (some (labels (.vertices .scan))) P
    (fun l => atLabels (.endpoints l)) b₁ input
    (by simpa using g₁) (by simpa using s₁) (by simpa using t₁) ambient
  have r₃ := GraphTokenMachine.tokensTrace .vertex (tokenSlots slots false)
    (fun l => labels (.vertices l)) (some (labels (.edges .scan))) P
    (fun l => atLabels (.vertices l)) b₂ input
    (by simpa using g₂) (by simpa using s₂) ambient
  have r₄ := GraphTokenMachine.tokensTrace .edge (tokenSlots slots true)
    (fun l => labels (.edges l)) exit P (fun l => atLabels (.edges l)) b₃ input
    (by simpa using g₃) (by simpa using s₃) ambient
  exact joinTrace (joinTrace (joinTrace r₁ r₂) r₃) r₄

def preparationInTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, P (labels l) = instruction slots labels exit l)
    (base : K → List Bool) (input : GraphReductionInput)
    (graphWord : base (slots 0) = graphBits input)
    (scratchEmpty : base (slots 1) = []) (temporaryEmpty : base (slots 2) = [])
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (.threshold .scan)), GraphFieldMachine.clean ambient, base⟩
      (some ⟨exit, GraphFieldMachine.clean ambient, preparedTapes slots base input⟩)
      (14 * (graphBits input).length + 10) where
  steps := steps input
  evals_in_steps := preparationTrace slots labels exit P atLabels base input
    graphWord scratchEmpty temporaryEmpty ambient
  steps_le_m := steps_le input

end BinPackingGap.GraphPreparationMachine

namespace BinPackingGap.PackingMachineBlocks

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

inductive State
  | graph (state : GraphFieldMachine.State Unit)
  | arithmetic (state : BinaryAddMachine.State Unit)
  | emission (state : MachineFieldTemplate.State Unit)
  deriving DecidableEq, Fintype

def graphControl : MachineControlEmbedding.Control (GraphFieldMachine.State Unit) State where
  put := State.graph
  get
    | .graph s => s
    | _ => GraphFieldMachine.clean ()
  get_put _ := rfl

def arithmeticControl : MachineControlEmbedding.Control (BinaryAddMachine.State Unit) State where
  put := State.arithmetic
  get
    | .arithmetic s => s
    | _ => BinaryAddMachine.clean ()
  get_put _ := rfl

def emissionControl : MachineControlEmbedding.Control (MachineFieldTemplate.State Unit) State where
  put := State.emission
  get
    | .emission s => s
    | _ => (((), ()), none)
  get_put _ := rfl

variable {K : Type} [DecidableEq K]

def invoke {σ L : Type} [Fintype L] (control : MachineControlEmbedding.Control σ State)
    (initial : σ) (main : L) (program : L → TM2.Stmt (fun _ : K => Bool) L σ) :
    Code (K := K) (S := State) :=
  .seq (.atom (.load (fun _ => control.put initial) .done))
    (.routine L inferInstance main
      (fun l => MachineControlEmbedding.statement control id none (program l)))

theorem invokeExec {σ L : Type} [Fintype L]
    (control : MachineControlEmbedding.Control σ State)
    (initial : σ) (main : L) (program : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (start : Data K State) (finishState : σ) (finishTapes : K → List Bool) (steps : Nat)
    (run : (MachineComposition.advance (TM2.step program))^[steps]
      (some ⟨some main, initial, start.tapes⟩) =
      some ⟨none, finishState, finishTapes⟩) :
    Exec (invoke control initial main program) start (1 + steps)
      ⟨control.put finishState, finishTapes⟩ := by
  refine Exec.seq (Exec.atom (.load (fun _ => control.put initial) .done) start) ?_
  apply Exec.routine inferInstance main
    (fun l => MachineControlEmbedding.statement control id none (program l))
  have translated := MachineControlEmbedding.trace control id none program
    (fun l => MachineControlEmbedding.statement control id none (program l))
    (fun _ => rfl) steps ⟨some main, initial, start.tapes⟩
    ⟨none, finishState, finishTapes⟩ run
  simpa only [Action.eval, MachineControlEmbedding.configuration,
    MachineSubroutine.label, id_eq] using translated

theorem invokeExecInTime {σ L : Type} [Fintype L]
    (control : MachineControlEmbedding.Control σ State)
    (initial : σ) (main : L) (program : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (start : Data K State) (finishState : σ) (finishTapes : K → List Bool) (budget : Nat)
    (run : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, initial, start.tapes⟩ (some ⟨none, finishState, finishTapes⟩) budget) :
    ∃ steps ≤ budget + 1, Exec (invoke control initial main program) start steps
      ⟨control.put finishState, finishTapes⟩ := by
  refine ⟨1 + run.steps, ?_, ?_⟩
  · have h := run.steps_le_m
    omega
  · exact invokeExec control initial main program start finishState finishTapes
      run.steps run.evals_in_steps

def prepareGraph (slots : Fin 7 ↪ K) : Code (K := K) (S := State) :=
  invoke graphControl (GraphFieldMachine.clean ()) (.threshold .scan)
    (GraphPreparationMachine.instruction slots id none)

theorem prepareGraph_exec (slots : Fin 7 ↪ K) (start : Data K State)
    (input : GraphReductionInput) (graphWord : start.tapes (slots 0) = graphBits input)
    (scratchEmpty : start.tapes (slots 1) = []) (temporaryEmpty : start.tapes (slots 2) = []) :
    Exec (prepareGraph slots) start (1 + GraphPreparationMachine.steps input)
      ⟨.graph (GraphFieldMachine.clean ()),
        GraphPreparationMachine.preparedTapes slots start.tapes input⟩ := by
  apply invokeExec
  exact GraphPreparationMachine.preparationTrace slots id none
    (GraphPreparationMachine.instruction slots id none) (fun _ => rfl)
    start.tapes input graphWord scratchEmpty temporaryEmpty ()

theorem prepareGraph_cost (input : GraphReductionInput) :
    1 + GraphPreparationMachine.steps input ≤ 14 * (graphBits input).length + 11 := by
  have h := GraphPreparationMachine.steps_le input
  omega

def emitPool (field : Fin 2 → K) (scratch output counter : K) :
    Code (K := K) (S := State) :=
  invoke emissionControl (((), ()), none) .guard
    (PackingPoolMachine.instruction field scratch output counter id none)

theorem emitPool_exec
    (field : Fin 2 → K) (scratch output counter : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (fieldCounter : ∀ j, field j ≠ counter)
    (scratchOutput : scratch ≠ output) (scratchCounter : scratch ≠ counter)
    (outputCounter : output ≠ counter)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (numerator denominator : List Bool)
    (numWord : base (field 0) = numerator) (denWord : base (field 1) = denominator)
    (startState : State) (suffix : List Bool) (n : Nat) :
    ∃ steps ≤ n * (3 * (numerator.length + denominator.length) + 9) + 3,
      Exec (emitPool field scratch output counter)
        ⟨startState, MachineUnaryCounter.counterTapes counter base n suffix⟩ steps
        ⟨.emission (((), ()), none), MachineUnaryCounter.counterTapes counter
          (Function.update base output
            (PackingPoolMachine.repeatWord
              (PackingPoolMachine.record numerator denominator).reverse n ++ base output))
          0 suffix⟩ := by
  have run := PackingPoolMachine.poolInTime field scratch output counter
    fieldScratch fieldOutput fieldCounter scratchOutput scratchCounter outputCounter
    id none (PackingPoolMachine.instruction field scratch output counter id none)
    (fun _ => rfl) base scratchEmpty numerator denominator numWord denWord () suffix n
  have lifted := invokeExecInTime emissionControl (((), ()), none) .guard
    (PackingPoolMachine.instruction field scratch output counter id none)
    ⟨startState, MachineUnaryCounter.counterTapes counter base n suffix⟩
    (((), ()), none) _ _ run
  simpa only [emitPool, emissionControl, Nat.add_assoc, Nat.reduceAdd] using lifted

end BinPackingGap.PackingMachineBlocks

namespace BinPackingGap.PackingArithmeticProgram

open FiniteTapeProgram PackingMachineBlocks

variable {K : Type} [DecidableEq K]

def code (body : Code (K := K) (S := BinaryAddMachine.State Unit)) :
    Code (K := K) (S := State) :=
  invoke arithmeticControl (BinaryAddMachine.clean ()) body.entry
    (body.instruction id none)

theorem exec (body : Code (K := K) (S := BinaryAddMachine.State Unit))
    (before after : K → List Bool) (steps : Nat) (state : State)
    (run : Exec body ⟨BinaryAddMachine.clean (), before⟩ steps
      ⟨BinaryAddMachine.clean (), after⟩) :
    Exec (code body) ⟨state, before⟩ (1 + steps)
      ⟨.arithmetic (BinaryAddMachine.clean ()), after⟩ := by
  exact invokeExec arithmeticControl (BinaryAddMachine.clean ()) body.entry
    (body.instruction id none) ⟨state, before⟩ (BinaryAddMachine.clean ()) after steps
    (run.trace (body.instruction id none) id none (fun _ => rfl))

theorem exec_in_time (body : Code (K := K) (S := BinaryAddMachine.State Unit))
    (before after : K → List Bool) (budget : Nat) (state : State)
    (run : ∃ steps ≤ budget, Exec body ⟨BinaryAddMachine.clean (), before⟩ steps
      ⟨BinaryAddMachine.clean (), after⟩) :
    ∃ steps ≤ budget + 1, Exec (code body) ⟨state, before⟩ steps
      ⟨.arithmetic (BinaryAddMachine.clean ()), after⟩ := by
  obtain ⟨steps, bound, actual⟩ := run
  exact ⟨1 + steps, by omega, exec body before after steps state actual⟩

end BinPackingGap.PackingArithmeticProgram

namespace BinPackingGap.PackingCountedProgram

open FiniteTapeProgram PackingMachineBlocks
open scoped BigOperators

variable {K : Type} [DecidableEq K]

def guardState (head : Option Bool) : State :=
  .arithmetic ((((), false), none), head)

def guard (counter : K) : Action K State :=
  .pop counter (fun _ head => guardState head) .done

def more : State → Bool
  | .arithmetic state => state.2.isSome
  | _ => false

def loop (counter : K) (body : Code (K := K) (S := State)) : Code (K := K) (S := State) :=
  .loop (guard counter) more body

def counterTapes (counter : K) (base : K → List Bool) (n : Nat) : K → List Bool :=
  Function.update base counter (List.replicate n true)

theorem guard_succ (counter : K) (base : K → List Bool) (n : Nat) (state : State) :
    (guard counter).eval ⟨state, counterTapes counter base (n + 1)⟩ =
      ⟨guardState (some true), counterTapes counter base n⟩ := by
  simp [guard, Action.eval, counterTapes, List.replicate_succ]

theorem guard_zero (counter : K) (base : K → List Bool) (state : State) :
    (guard counter).eval ⟨state, counterTapes counter base 0⟩ =
      ⟨guardState none, counterTapes counter base 0⟩ := by
  simp [guard, Action.eval, counterTapes]

def totalBudget (bodyCost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, bodyCost r) + n + 1

@[simp] theorem totalBudget_zero (bodyCost : Nat → Nat) : totalBudget bodyCost 0 = 1 := by
  simp [totalBudget]

theorem totalBudget_succ (bodyCost : Nat → Nat) (n : Nat) :
    totalBudget bodyCost (n + 1) = bodyCost n + totalBudget bodyCost n + 1 := by
  simp only [totalBudget, Finset.sum_range_succ]
  omega

theorem exec (counter : K) (body : Code (K := K) (S := State))
    (base : Nat → K → List Bool) (state : Nat → State) (bodyCost : Nat → Nat) (n : Nat)
    (bodyRuns : ∀ r, r < n → ∃ steps ≤ bodyCost r,
      Exec body ⟨guardState (some true), counterTapes counter (base (r + 1)) r⟩ steps
        ⟨state r, counterTapes counter (base r) r⟩) :
    ∃ steps ≤ totalBudget bodyCost n,
      Exec (loop counter body) ⟨state n, counterTapes counter (base n) n⟩ steps
        ⟨guardState none, counterTapes counter (base 0) 0⟩ := by
  revert bodyRuns
  induction n with
  | zero =>
      intro _
      refine ⟨1, by simp, ?_⟩
      have h : more ((guard counter).eval
          ⟨state 0, counterTapes counter (base 0) 0⟩).state = false := by
        rw [guard_zero]
        rfl
      simpa only [loop, guard_zero] using
        (Exec.loop_false (a := body) h)
  | succ n ih =>
      intro bodyRuns
      obtain ⟨tailSteps, htail, tailRun⟩ := ih (fun r hr => bodyRuns r (by omega))
      obtain ⟨bodySteps, hbody, bodyRun⟩ := bodyRuns n (by omega)
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [totalBudget_succ]
        omega
      · have h : more ((guard counter).eval
            ⟨state (n + 1), counterTapes counter (base (n + 1)) (n + 1)⟩).state = true := by
          rw [guard_succ]
          rfl
        have bodyRun' : Exec body ((guard counter).eval
            ⟨state (n + 1), counterTapes counter (base (n + 1)) (n + 1)⟩) bodySteps
            ⟨state n, counterTapes counter (base n) n⟩ := by
          rw [guard_succ]
          exact bodyRun
        exact Exec.loop_true h bodyRun' tailRun

theorem totalBudget_le (bodyCost : Nat → Nat) (n bound : Nat)
    (bounded : ∀ r, r < n → bodyCost r ≤ bound) :
    totalBudget bodyCost n ≤ n * (bound + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, bodyCost r) ≤ n * bound := by
    calc
      _ ≤ ∑ _r ∈ Finset.range n, bound :=
        Finset.sum_le_sum (fun r hr => bounded r (Finset.mem_range.mp hr))
      _ = _ := by simp
  simp only [totalBudget, Nat.mul_add, Nat.mul_one]
  omega

end BinPackingGap.PackingCountedProgram

end OAI
