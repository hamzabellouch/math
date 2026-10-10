import Mathlib
import OAI.Computability.MinUncut.Machines.PoweringMachineRowHeaders
import OAI.Computability.MinUncut.PCP.PoweringTableLayout

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Command (d n : Nat) := Fin (PoweringTableLayout.blockSize d n)

def ports {d n : Nat} (j : Command d n) : Fin (n + 1) → Fin d :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).1

def direction {d n : Nat} (j : Command d n) : Bool :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).2

def commands (d n : Nat) : List (Command d n) := (List.ofFn id).reverse

@[simp] theorem commands_length (d n : Nat) :
    (commands d n).length = PoweringTableLayout.blockSize d n := by
  simp only [commands, List.length_reverse, List.length_ofFn]

abbrev LocalLabel (j : Command d n) := PoweringMachineRowBody.Label n (ports j) (direction j)
abbrev SequenceLabel (ops : List (Command d n)) := MachineFiniteSequence.Label LocalLabel ops
abbrev Label (d n : Nat) := SequenceLabel (commands d n)
abbrev State (d n : Nat) := PoweringMachineRowBody.State d n

def sequenceEntry (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j)) ops labels exit

def entry (d n : Nat) (labels : Label d n → Λ) (exit : Option Λ) : Option Λ :=
  sequenceEntry (commands d n) labels exit

def sequenceInstruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : SequenceLabel ops → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  MachineFiniteSequence.instruction LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    ops labels exit

def instruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (labels : Label d n → Λ) (exit : Option Λ) :
    Label d n → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  sequenceInstruction n placement output (commands d n) labels exit

def result (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (j : Command d n) (base : K → List Bool) :
    K → List Bool :=
  PoweringMachineRowBody.finalTapes graph n placement output vertex (ports j) (direction j) base

def sequenceTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    K → List Bool :=
  MachineFiniteSequence.resultOf (result graph n placement output vertex) ops base

def finalTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool) : K → List Bool :=
  sequenceTapes graph n placement output vertex (commands d n) base

def sequenceSteps (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j)) ops base

def costSum (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    List (Command d n) → Nat
  | [] => 0
  | j :: ops => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
      costSum graph vertex n ops

theorem sequenceSteps_eq (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    sequenceSteps graph n placement output vertex ops base = costSum graph vertex n ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        sequenceSteps graph n placement output vertex ops
          (result graph n placement output vertex j base) = _
      rw [ih]
      rfl

def steps (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) : Nat :=
  costSum graph vertex n (commands d n)

def budget (d n inputLength : Nat) : Nat :=
  PoweringTableLayout.blockSize d n * PoweringMachineRowBody.budget d n inputLength

theorem costSum_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ops : List (Command d n)) :
    costSum graph vertex n ops ≤
      ops.length * PoweringMachineRowBody.budget d n (PortTables.tableBits graph).length := by
  induction ops with
  | nil => simp only [costSum, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons j ops ih =>
      have hfirst := PoweringMachineRowBody.steps_le graph vertex n (ports j) (direction j)
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        costSum graph vertex n ops ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add hfirst ih

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    steps graph vertex n ≤ budget d n (PortTables.tableBits graph).length := by
  simpa only [steps, budget, commands_length] using costSum_le graph vertex n (commands d n)

theorem sequenceTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n))
    (labels : SequenceLabel ops → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction n placement output ops labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[sequenceSteps graph n placement output vertex ops base]
      (some ⟨sequenceEntry ops labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        sequenceTapes graph n placement output vertex ops base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j))
    program (PoweringMachineRowBody.Ready graph n placement vertex suffix)
    (fun _ => PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)) id ops
  · intro j _ tapes good
    exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
      vertex (ports j) (direction j) tapes suffix good
  · intro j _ localLabels localExit atLocal tapes good
    exact PoweringMachineRowBody.rowTrace graph n placement distinct output outside vertex
      (ports j) (direction j) localLabels localExit program atLocal tapes suffix good
  · exact atLabels
  · exact ready

theorem vertexTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n]
      (some ⟨entry d n labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩ := by
  have h := sequenceTrace graph n placement distinct output outside vertex (commands d n)
    labels exit program atLabels base suffix ready
  rw [sequenceSteps_eq] at h
  exact h

theorem sequenceTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (sequenceTapes graph n placement output vertex ops base) := by
  induction ops generalizing base with
  | nil => exact ready
  | cons j ops ih =>
      apply ih
      exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
        vertex (ports j) (direction j) base suffix ready

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (finalTapes graph n placement output vertex base) :=
  sequenceTapes_ready graph n placement distinct output outside vertex (commands d n) base suffix ready

theorem sequenceTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    sequenceTapes graph n placement output vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) k = _
      rw [ih]
      exact PoweringMachineRowBody.finalTapes_other graph n placement output vertex
        (ports j) (direction j) base k hout outside

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex base k = base k :=
  sequenceTapes_other graph n placement output vertex (commands d n) base k hout outside

def rowBits (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) : List Bool :=
  encodeWords (PoweringMachineRowBody.rowWords graph n vertex (ports j) (direction j))

theorem blockIndex_eq_encodeDart (n : Nat) (vertex : Fin vertices) (j : Command d n) :
    PoweringTableLayout.blockIndex d n vertex j =
      PoweringEnumeration.encodeDart vertices d n (direction j, vertex, ports j) := by
  have h := PoweringTableLayout.blockIndex_eq_encodeDart d n vertex (ports j) (direction j)
  simp only [ports, direction, Prod.mk.eta] at h
  erw [Equiv.apply_symm_apply] at h
  exact h

theorem rowBits_eq (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) :
    rowBits graph n vertex j = encodeWords (GenericGraphTables.rowWords
      (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
  rw [blockIndex_eq_encodeDart]
  rfl

theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rows_eq_vertexRowBits (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) :
    (List.ofFn id : List (Command d n)).flatMap (rowBits graph n vertex) =
      PoweringTableLayout.vertexRowBits graph n vertex := by
  have hrows : (List.ofFn id : List (Command d n)).map
      (fun j => (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) =
      List.ofFn (fun j : Command d n =>
        (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
    simp only [List.map_ofFn, Function.comp_id]
  calc
    _ = (List.ofFn id : List (Command d n)).flatMap (fun j => encodeWords
        (GenericGraphTables.rowWords
          (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j])) := by
      apply congrArg (List.flatMap · (List.ofFn id))
      funext j
      exact rowBits_eq graph n vertex j
    _ = PoweringTableLayout.vertexRowBits graph n vertex := by
      unfold PoweringTableLayout.vertexRowBits PoweringTableLayout.vertexRowWords
        PoweringTableLayout.vertexRows
      rw [encodeWords_flatMap]
      erw [← hrows, List.flatMap_map]
      rfl

theorem sequenceTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    sequenceTapes graph n placement output vertex ops base output =
      ops.reverse.flatMap (rowBits graph n vertex) ++ base output := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      have nextReady := PoweringMachineRowBody.finalTapes_ready graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) output = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineRowBody.finalTapes_output graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, rowBits]

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex base output =
      PoweringTableLayout.vertexRowBits graph n vertex ++ base output := by
  rw [finalTapes, sequenceTapes_output graph n placement distinct output outside vertex
    (commands d n) base suffix ready]
  simp only [commands, List.reverse_reverse, rows_eq_vertexRowBits]

def vertexInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry d n labels exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩
      (some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩)
      (budget d n (PortTables.tableBits graph).length) where
  steps := steps graph vertex n
  evals_in_steps := vertexTrace graph n placement distinct output outside vertex labels exit
    program atLabels base suffix ready
  steps_le_m := steps_le graph vertex n

end MinUncutGames.Foundations.Complexity.PoweringMachineVertex

namespace MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K
abbrev State := PoweringMachineVertex.State

structure Ready (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (base : K → List Bool) : Prop where
  table : base (placement (.inl 0)) = PortTables.tableBits graph
  scratch : base (placement (.inl 5)) = []
  leftCopy : base (placement (.inl 8)) = []
  rightCopy : base (placement (.inl 9)) = []
  data : base (placement (.inl 10)) = []

def counter (placement : Placement K n) (base : K → List Bool) (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

theorem counter_other (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

theorem ready_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (ready : Ready graph n placement base) (vertex : Fin vertices) :
    PoweringMachineRowBody.Ready graph n placement vertex [] (counter placement base vertex.val) := by
  constructor
  · constructor
    · rw [counter_other placement distinct base vertex.val 0 (by decide)]
      exact ready.table
    · simp only [counter, MachineUnaryCounter.counterTapes_counter]
    · rw [counter_other placement distinct base vertex.val 5 (by decide)]
      exact ready.scratch
    · rw [counter_other placement distinct base vertex.val 8 (by decide)]
      exact ready.leftCopy
    · rw [counter_other placement distinct base vertex.val 9 (by decide)]
      exact ready.rightCopy
  · rw [counter_other placement distinct base vertex.val 10 (by decide)]
    exact ready.data

omit [DecidableEq K] in
theorem ready_of_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (base : K → List Bool) (vertex : Fin vertices)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex [] base) :
    Ready graph n placement base :=
  ⟨ready.1.table, ready.1.scratch, ready.1.leftCopy, ready.1.rightCopy, ready.2⟩

def vertexStart (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) : Λ :=
  (PoweringMachineVertex.entry d n labels (some guardLabel)).getD guardLabel

theorem vertexEntry (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    PoweringMachineVertex.entry d n labels (some guardLabel) =
      some (vertexStart d n labels guardLabel) := by
  unfold vertexStart PoweringMachineVertex.entry PoweringMachineVertex.sequenceEntry
  have h : ∀ (commands : List (PoweringMachineVertex.Command d n))
      (labels : MachineFiniteSequence.Label PoweringMachineVertex.LocalLabel commands → Λ),
      MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel) =
      some ((MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel)).getD guardLabel) := by
    intro commands labels
    cases commands <;> rfl
  exact h _ labels

def bridge (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  .goto (fun _ => vertexStart d n labels guardLabel)

def finalTapes (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (output : K) : (remaining : Nat) → remaining ≤ vertices → (K → List Bool) → K → List Bool
  | 0, _, base => counter placement base 0
  | r + 1, bounded, base =>
      finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output ⟨r, by omega⟩
          (counter placement base r))

def steps (graph : PortTables.Table vertices d) (n : Nat) :
    (remaining : Nat) → remaining ≤ vertices → Nat
  | 0, _ => 1
  | r + 1, bounded =>
      2 + PoweringMachineVertex.steps graph ⟨r, by omega⟩ n + steps graph n r (by omega)

theorem steps_le (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    steps graph n remaining bounded ≤
      remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1 := by
  induction remaining with
  | zero => simp [steps]
  | succ r ih =>
      have hv := PoweringMachineVertex.steps_le graph (⟨r, by omega⟩ : Fin vertices) n
      have hi := ih (by omega)
      simp only [steps, Nat.add_mul, Nat.one_mul]
      omega

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    Ready graph n placement (finalTapes graph n placement output remaining bounded base) := by
  induction remaining generalizing base with
  | zero =>
      constructor
      · rw [finalTapes, counter_other placement distinct base 0 0 (by decide)]
        exact ready.table
      · rw [finalTapes, counter_other placement distinct base 0 5 (by decide)]
        exact ready.scratch
      · rw [finalTapes, counter_other placement distinct base 0 8 (by decide)]
        exact ready.leftCopy
      · rw [finalTapes, counter_other placement distinct base 0 9 (by decide)]
        exact ready.rightCopy
      · rw [finalTapes, counter_other placement distinct base 0 10 (by decide)]
        exact ready.data
  | succ r ih =>
      apply ih
      apply ready_of_vertex graph n placement _ (⟨r, by omega⟩ : Fin vertices)
      exact PoweringMachineVertex.finalTapes_ready graph n placement distinct output outside
        ⟨r, by omega⟩ _ [] (ready_vertex graph n placement distinct base ready _)

def prefixRows (graph : PortTables.Table vertices d) (n : Nat) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixRows graph n r ++
      if h : r < vertices then PoweringTableLayout.vertexRowBits graph n ⟨r, h⟩ else []

theorem prefixRows_ofFn (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    prefixRows graph n remaining =
      (List.ofFn (fun i : Fin remaining =>
        PoweringTableLayout.vertexRowBits graph n (Fin.castLE bounded i))).flatten := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      have hr : r < vertices := by omega
      rw [prefixRows, dite_eq_left hr, List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      change prefixRows graph n r ++ PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩ =
        (List.ofFn (fun i : Fin r => PoweringTableLayout.vertexRowBits graph n
          (Fin.castLE (show r ≤ vertices by omega) i))).flatten ++
          PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩
      rw [ih]

theorem prefixRows_all (graph : PortTables.Table vertices d) (n : Nat) :
    prefixRows graph n vertices =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [prefixRows_ofFn graph n vertices (Nat.le_refl _)]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    finalTapes graph n placement output remaining bounded base output =
      prefixRows graph n remaining ++ base output := by
  induction remaining generalizing base with
  | zero =>
      exact MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _)
        base 0 []
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      have vertexReady := ready_vertex graph n placement distinct base ready vertex
      have nextReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      change finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output vertex current) output = _
      rw [ih (by omega) _ (ready_of_vertex graph n placement _ vertex nextReady),
        PoweringMachineVertex.finalTapes_output graph n placement distinct output outside
          vertex current [] vertexReady]
      have hc : current output = base output :=
        MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _) base r []
      rw [hc, prefixRows, dite_eq_left vertex.isLt, List.append_assoc]

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (output : K) (remaining : Nat)
    (bounded : remaining ≤ vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output remaining bounded base k = base k := by
  induction remaining generalizing base with
  | zero => exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base 0 []
  | succ r ih =>
      rw [finalTapes, ih, PoweringMachineVertex.finalTapes_other graph n placement output
        ⟨r, by omega⟩ _ k hout outside]
      exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base r []

theorem loopTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    (advance (TM2.step program))^[steps graph n remaining bounded]
      (some ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩) =
      some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩ := by
  let initial := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  induction remaining generalizing base with
  | zero =>
      simpa only [steps, finalTapes, counter, initial, PoweringMasterState.clean,
        PoweringMasterState.withBuffer] using
        MachineUnaryCounter.guardTrace_zero (placement (.inl 1)) guardLabel bridgeLabel exitLabel
          program atGuard base [] initial.1 none
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      let next := PoweringMachineVertex.finalTapes graph n placement output vertex current
      have vertexReady : PoweringMachineRowBody.Ready graph n placement vertex [] current :=
        ready_vertex graph n placement distinct base ready vertex
      have nextVertexReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      have nextReady : Ready graph n placement next :=
        ready_of_vertex graph n placement next vertex nextVertexReady
      have sameCounter : counter placement next r = next := by
        have hs := nextVertexReady.1.source
        change next (placement (.inl 1)) = encodeWord r ++ [] at hs
        unfold counter MachineUnaryCounter.counterTapes
        rw [← hs]
        exact Function.update_eq_self _ _
      have tailRun := ih (by omega) next nextReady
      rw [sameCounter] at tailRun
      have guardRun : advance (TM2.step program)
          (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) =
          some ⟨some bridgeLabel, initial, current⟩ := by
        simpa only [advance_some, current, counter, initial, PoweringMasterState.clean,
          PoweringMasterState.withBuffer] using
          MachineUnaryCounter.guardStep_succ (placement (.inl 1)) guardLabel bridgeLabel exitLabel
            program atGuard base r [] initial.1 none
      have bridgeRun : advance (TM2.step program)
          (some ⟨some bridgeLabel, initial, current⟩) =
          some ⟨PoweringMachineVertex.entry d n labels (some guardLabel), initial, current⟩ := by
        change some (TM2.stepAux (program bridgeLabel) initial current) = _
        rw [atBridge, vertexEntry]
        rfl
      have vertexRun := PoweringMachineVertex.vertexTrace graph n placement distinct output outside
        vertex labels (some guardLabel) program atVertex current [] vertexReady
      change (advance (TM2.step program))^[2 + PoweringMachineVertex.steps graph vertex n +
          steps graph n r (by omega)]
        (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) = _
      rw [show 2 + PoweringMachineVertex.steps graph vertex n + steps graph n r (by omega) =
          (steps graph n r (by omega) + PoweringMachineVertex.steps graph vertex n) + 1 + 1 by omega,
        Function.iterate_succ_apply, guardRun, Function.iterate_succ_apply, bridgeRun,
        Function.iterate_add_apply, vertexRun]
      exact tailRun

def loopInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩
      (some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩)
      (remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1) where
  steps := steps graph n remaining bounded
  evals_in_steps := loopTrace graph n placement distinct output outside guardLabel bridgeLabel
    exitLabel labels program atGuard atBridge atVertex remaining bounded base ready
  steps_le_m := steps_le graph n remaining bounded

end MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop

namespace MinUncutGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (labels : Label enumeration output → Λ) :
    Label enumeration output → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .inl l => copyInstruction headerD scratch output (fun q => labels (.inl q))
      (some (labels (.inr (.inl .seed)))) l
  | .inr (.inl l) => copyInstruction headerV scratch output
      (fun q => labels (.inr (.inl q)))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
        (fun q => labels (.inr (.inr q))) none) l
  | .inr (.inr l) => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration output) (fun q => labels (.inr (.inr q))) none l

def program (enumeration : Fin N ≃ K) (headerV headerD output scratch : K) :
    Label enumeration output →
      TM2.Stmt (Alphabet (K := K)) (Label enumeration output) (σ × Option Bool) :=
  instruction enumeration headerV headerD output scratch id

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

def copySteps (n m : Nat) : Nat := (2 * (m + 1) + 1) + (2 * (n + 1) + 1)

theorem copySteps_eq (n m : Nat) : copySteps n m = 2 * (n + m) + 6 := by
  unfold copySteps
  omega

def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

def budget (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + (MachineDrainMany.lengthSum (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) + (MachineDrainMany.workTapes enumeration output).length)

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem traceAt (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (labels : Label enumeration output → Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      instruction enumeration headerV headerD output scratch labels l)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps enumeration output base n m]
      (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ := by
  have hd := MachineUnaryAffineAt.seededAffineTrace headerD scratch output hds hdo hso 1 0
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (.inr (.inl .seed)))) target
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base m suffixD wordD scratchEmpty ambient register
  simp only [Nat.one_mul, Nat.add_zero] at hd
  change (advance (TM2.step target))^[2 * (m + 1) + 1]
    (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
    some ⟨some (labels (.inr (.inl .seed))), (ambient, none), afterD output base m⟩ at hd
  have wordV' : afterD output base m headerV = encodeWord n ++ suffixV := by
    simpa only [afterD, Function.update_of_ne hvo] using wordV
  have scratchEmpty' : afterD output base m scratch = [] := by
    simpa only [afterD, Function.update_of_ne hso] using scratchEmpty
  have hv := MachineUnaryAffineAt.seededAffineTrace headerV scratch output hvs hvo hso 1 0
    (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
    (labels (.inr (.inl .restore)))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
      (fun q => labels (.inr (.inr q))) none)
    target (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
    (atLabels (.inr (.inl .restore))) (afterD output base m) n suffixV
    wordV' scratchEmpty' ambient none
  simp only [Nat.one_mul, Nat.add_zero] at hv
  have copied : Function.update (afterD output base m) output
      (encodeWord n ++ afterD output base m output) = afterHeaders output base n m := by
    simp only [afterD, afterHeaders, Function.update_self, Function.update_idem,
      encodeWords, List.append_nil, List.append_assoc]
  rw [copied] at hv
  have cleaned := MachineDrainMany.cleanupTrace enumeration output
    (fun q => labels (.inr (.inr q))) target (fun l => atLabels (.inr (.inr l)))
    (afterHeaders output base n m) ambient
  rw [afterHeaders_output] at cleaned
  have total := trace_trans _ (trace_trans _ hd hv) cleaned
  simpa only [steps, copySteps] using total

theorem trace (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program enumeration headerV headerD output scratch)))^[
      steps enumeration output base n m]
      (some ⟨some (.inl .seed), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ :=
  traceAt enumeration headerV headerD output scratch hvs hvo hds hdo hso id
    (program enumeration headerV headerD output scratch) (fun _ => rfl)
    base n m suffixV suffixD wordV wordD scratchEmpty ambient register

theorem steps_le_budget (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m : Nat) :
    steps enumeration output base n m ≤ budget enumeration output base n m :=
  Nat.add_le_add_left (MachineDrainMany.steps_le
    (MachineDrainMany.workTapes enumeration output) (afterHeaders output base n m)) _

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

def execution (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program enumeration headerV headerD output scratch))
      ⟨some (.inl .seed), (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩)
      (budget enumeration output base n m) where
  steps := steps enumeration output base n m
  evals_in_steps := trace enumeration headerV headerD output scratch hvs hvo hds hdo hso
    base n m suffixV suffixD wordV wordD scratchEmpty ambient register
  steps_le_m := steps_le_budget enumeration output base n m

end MinUncutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
