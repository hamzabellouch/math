import OAI.Computability.BinPacking.Computation.MachineLazyRows
import OAI.Computability.BinPacking.Computation.MachineRegularInternalRow
import OAI.Computability.BinPacking.PCP.PreprocessingRegularBounds

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

abbrev Tape := MachineRegularOriginalRow.Tape
abbrev Alphabet := MachineRegularOriginalRow.Alphabet
abbrev State := MachineRegularOriginalRow.State

inductive Label
  | row (label : MachineRegularOriginalRow.Label)
  | query | scan | rawReverse | computedReverse | relation
  deriving DecidableEq, Fintype

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .row l => MachineRegularOriginalRow.instruction q (fun l => labels (.row l))
      (some (labels .query)) l
  | .query => MachineDrain.drain 2 (labels .query) (some (labels .scan))
  | .scan => MachineDrain.drain 3 (labels .scan) (some (labels .rawReverse))
  | .rawReverse => MachineDrain.drain 4 (labels .rawReverse) (some (labels .computedReverse))
  | .computedReverse => MachineDrain.drain 6 (labels .computedReverse) (some (labels .relation))
  | .relation => MachineDrain.drain 7 (labels .relation) exit

def cleanupTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update base 2 []) 3 []) 4 []) 6 []) 7 []

def cleanupSteps (base : Tape → List Bool) : Nat :=
  ((base 2).length + 1) + ((base 3).length + 1) + ((base 4).length + 1) +
    ((base 6).length + 1) + ((base 7).length + 1)

private theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (base : Tape → List Bool) (state : State σ) :
    (advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (labels .query), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes base⟩ := by
  let t1 := Function.update base (2 : Tape) []
  let t2 := Function.update t1 (3 : Tape) []
  let t3 := Function.update t2 (4 : Tape) []
  let t4 := Function.update t3 (6 : Tape) []
  have h0 := MachineDrain.drainTrace (2 : Tape) (labels .query) (some (labels .scan))
    program (code .query) base (base 2) state.1 state.2
  have h1 := MachineDrain.drainTrace (3 : Tape) (labels .scan) (some (labels .rawReverse))
    program (code .scan) t1 (t1 3) state.1 none
  have h2 := MachineDrain.drainTrace (4 : Tape) (labels .rawReverse) (some (labels .computedReverse))
    program (code .rawReverse) t2 (t2 4) state.1 none
  have h3 := MachineDrain.drainTrace (6 : Tape) (labels .computedReverse) (some (labels .relation))
    program (code .computedReverse) t3 (t3 6) state.1 none
  have h4 := MachineDrain.drainTrace (7 : Tape) (labels .relation) exit
    program (code .relation) t4 (t4 7) state.1 none
  simp only [Function.update_eq_self] at h0 h1 h2 h3 h4
  simp only [t1, t2, t3, t4, Function.update_of_ne (by decide : (3 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 6),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 2)] at h1 h2 h3 h4
  exact join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4

structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop
    extends MachineRegularOriginalRow.Input t e base where
  queryEmpty : base 2 = []
  scanEmpty : base 3 = []

theorem cleanup_frame (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupTapes (MachineRegularOriginalRow.finalTapes q t e base) =
      Function.update base 9
        (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)) := by
  funext k
  fin_cases k <;>
    simp [cleanupTapes, MachineRegularOriginalRow.finalTapes,
      MachineRegularOriginalRow.affined, MachineRegularOriginalRow.copied,
      MachineRegularOriginalRow.looked, MachineAffineLookup.finalTapes,
      MachinePreservingLookup.finalTapes, MachineLookup.tapes,
      MachineRegularOriginalRow.lookupTape, input.queryEmpty, input.scanEmpty,
      input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem suffix_length_le (t : Table) (e : Fin t.darts) :
    (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length ≤ (tableBits t).length := by
  have hlength : (tableBits t).length =
      (encodeWords (MachineRegularOriginalRow.prefixWords t e)).length +
        ((encodeWords (rowWords t.rows[e])).length +
          (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length) := by
    rw [tableBits, MachineRegularOriginalRow.tableWords_at_row,
      encodeWords_append, encodeWords_append, List.length_append, List.length_append]
  omega

theorem cleanupSteps_eq (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) =
      (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length +
        (q + 2) * t.rows[e].reverseIndex.val + q +
          (encodeWords (relationWords t.rows[e].relation)).length + 8 := by
  have hquery : MachineRegularOriginalRow.finalTapes q t e base 2 = encodeWord 0 := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 7),
      Function.update_of_ne (by decide : (2 : Tape) ≠ 3)]
    change MachineLookup.tapes (2 : Tape) 3 4 base
      (encodeWord 0 ++ base 2)
      (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
      (encodeWord t.rows[e].reverseIndex.val ++ base 4) 2 = _
    rw [MachineLookup.tapes_index _ _ _ (by decide) (by decide), input.queryEmpty,
      List.append_nil]
  have hscan : MachineRegularOriginalRow.finalTapes q t e base 3 =
      encodeWords (MachineRegularOriginalRow.suffixWords t e) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 7), Function.update_self,
      input.scanEmpty, List.append_nil]
  have hraw : MachineRegularOriginalRow.finalTapes q t e base 4 =
      encodeWord t.rows[e].reverseIndex.val := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 6), MachineRegularOriginalRow.copied_reverse,
      input.reverseEmpty, List.append_nil]
  have hcomputed : MachineRegularOriginalRow.finalTapes q t e base 6 =
      encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (6 : Tape) ≠ 9), MachineRegularOriginalRow.affined_reverse,
      input.computedEmpty, List.append_nil]
  have hrelation : MachineRegularOriginalRow.finalTapes q t e base 7 =
      encodeWords (relationWords t.rows[e].relation) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (7 : Tape) ≠ 9), MachineRegularOriginalRow.affined_relation,
      input.relationEmpty, List.append_nil]
  simp only [cleanupSteps, hquery, hscan, hraw, hcomputed, hrelation, encodeWord_length]
  ring

theorem cleanupSteps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) ≤
      (q + 3) * (tableBits t).length + q + 8200 := by
  rw [cleanupSteps_eq q t e base input]
  have hsuffix := suffix_length_le t e
  have htable := tableWords_length_le_bits t
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hmul := Nat.mul_le_mul_left (q + 2) hr
  have hrel := relationBits_length_le t.rows[e].relation
  nlinarith

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineRegularOriginalRow.steps q t e base +
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base)

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (5 * q + 20) * inputLength + 2 * outputLength + 5 * q + 40995

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hrow := MachineRegularOriginalRow.steps_le q t e base
  have hclean := cleanupSteps_le q t e base input
  unfold steps timeBound MachineRegularOriginalRow.timeBound at *
  nlinarith

theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.row (.lookup .seed))),
        ((ambient, MachineRegularOriginalRow.zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, MachineRegularOriginalRow.zeroBuffer), none),
        Function.update base 9
          (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ := by
  have row := MachineRegularOriginalRow.traceAt q (fun l => labels (.row l))
    (some (labels .query)) program (fun l => code (.row l)) t e base input.toInput ambient register
  have clean := cleanupTraceAt q labels exit program code
    (MachineRegularOriginalRow.finalTapes q t e base)
    ((ambient, MachineRegularOriginalRow.zeroBuffer), none)
  rw [cleanup_frame q t e base input] at clean
  exact join_trace row clean

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := 1
  k₁ := 9
  Γ := Alphabet
  Λ := Label
  main := .row (.lookup .seed)
  σ := State Unit
  initialState := (((), MachineRegularOriginalRow.zeroBuffer), none)
  m := instruction q id none

def machineInTime (H : BaseTable) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine internalDegree).step
      ⟨some (.row (.lookup .seed)), (((), MachineRegularOriginalRow.zeroBuffer), register), base⟩
      (some ⟨none, (((), MachineRegularOriginalRow.zeroBuffer), none),
        Function.update base (9 : Tape)
          (base (9 : Tape) ++ encodeWords (rowWords (MachineRegularOriginalRow.inheritedRow H t e)))⟩)
      (timeBound internalDegree (tableBits t).length (base (9 : Tape)).length) where
  steps := steps internalDegree t e base
  evals_in_steps := by
    change (advance (TM2.step (instruction internalDegree id none)))^[_] _ = _
    rw [MachineRegularOriginalRow.inheritedRow_words]
    exact traceAt internalDegree id none (instruction internalDegree id none)
      (fun _ => rfl) t e base input () register
  steps_le_m := steps_le internalDegree t e base input

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalClean

namespace BinPackingGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

abbrev PortLabel (q : Nat) := Fin q × CoreLabel q

def portEntry (q : Nat) (labels : PortLabel q → Λ) (exit : Option Λ) (k : Nat) :
    Option Λ :=
  if h : k < q then some (labels (⟨k, h⟩, coreEntry q)) else exit

def portInstruction (q : Nat) (positive : 0 < q) (labels : PortLabel q → Λ)
    (exit : Option Λ) (l : PortLabel q) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  coreInstruction q positive l.1 (fun s => labels (l.1, s))
    (portEntry q labels exit (l.1.val + 1)) l.2

def portBits {q : Nat} (bits : Fin q → List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => portBits bits k ++ if h : k < q then bits ⟨k, h⟩ else []

theorem portBits_eq {q : Nat} (bits : Fin q → List Bool) (k : Nat) (hk : k ≤ q) :
    portBits bits k = (List.ofFn (fun p : Fin k => bits ⟨p.val, lt_of_lt_of_le p.isLt hk⟩)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < q := by omega
    rw [portBits, dite_eq_left h, ih (by omega), List.ofFn_succ_last, List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

theorem portBits_all {q : Nat} (bits : Fin q → List Bool) :
    portBits bits q = (List.ofFn bits).flatten := by
  simpa only [Fin.eta] using portBits_eq bits q (Nat.le_refl q)

def rowBits (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) : List Bool :=
  encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p))

def portSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => portSteps t padding tables v x outputLength k +
      if h : k < q then coreSteps t padding tables v x ⟨k, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) k).length) else 0

private theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem portPrefixTrace (q : Nat) (positive : 0 < q)
    (labels : PortLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = portInstruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (output : List Bool) (ambient : σ)
    (k : Nat) (hk : k ≤ q) :
    (advance (TM2.step program))^[portSteps t padding tables v x output.length k]
      (some ⟨portEntry q labels exit 0, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨portEntry q labels exit k, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ portBits (rowBits t padding tables v x) k)⟩ := by
  induction k with
  | zero => simp only [portSteps, portBits, List.append_nil, Function.iterate_zero, id_eq]
  | succ k ih =>
    have h : k < q := by omega
    have first := ih (by omega)
    have second := coreTrace q positive ⟨k, h⟩ (fun s => labels (⟨k, h⟩, s))
      (portEntry q labels exit (k + 1)) program (fun s => code (⟨k, h⟩, s))
      t padding tables v x (output ++ portBits (rowBits t padding tables v x) k) ambient
    have he : portEntry q labels exit k = some (labels (⟨k, h⟩, coreEntry q)) := by
      simp only [portEntry, dite_eq_left h]
    rw [he] at first
    have total := joinTrace first second
    simpa only [portSteps, dite_eq_left h, List.length_append, portBits, rowBits,
      List.append_assoc] using total

theorem portTrace (q : Nat) (positive : 0 < q)
    (labels : PortLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = portInstruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[portSteps t padding tables v x output.length q]
      (some ⟨portEntry q labels exit 0, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ (List.ofFn (rowBits t padding tables v x)).flatten)⟩ := by
  simpa only [portEntry, lt_self_iff_false, dite_false, portBits_all] using
    portPrefixTrace q positive labels exit program code t padding tables v x output ambient q le_rfl

def originalTapes : MachineRegularOriginalClean.Tape → CoreTape :=
  ![1, 0, 10, 11, 12, 9, 24, 25, 26, 8]

def originalView : CoreTape → Option MachineRegularOriginalClean.Tape :=
  ![some 1, some 0, none, none, none, none, none, none, some 9, some 5,
    some 2, some 3, some 4, none, none, none, none, none, none, none,
    none, none, none, none, some 6, some 7, some 8]

theorem originalView_left (k : MachineRegularOriginalClean.Tape) :
    originalView (originalTapes k) = some k := by fin_cases k <;> rfl

theorem originalView_right (j : CoreTape) (k : MachineRegularOriginalClean.Tape)
    (h : originalView j = some k) : originalTapes k = j := by
  fin_cases j <;> simp [originalView] at h
  all_goals subst k; rfl

def originalStateEquiv (σ : Type) (q : Nat) :
    MachineRegularOriginalClean.State (σ × (Fin q × (Bool × MachineCloudSelect.Phase))) ≃
      CoreState σ q where
  toFun s := ((s.1.1.1, (s.1.2, s.1.1.2)), s.2)
  invFun s := (((s.1.1, s.1.2.2), s.1.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨a,b⟩,c⟩,d⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,c⟩⟩,d⟩; rfl

def originalCoreInstruction (q : Nat) (labels : MachineRegularOriginalClean.Label → Λ)
    (exit : Option Λ) (l : MachineRegularOriginalClean.Label) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  MachineCloudPadding.Placement.statement originalTapes labels exit
    (MachineStateEquiv.statement (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none l))

def originalMemory (graph : List Bool) (x : Nat) (output : List Bool) :
    MachineRegularOriginalClean.Tape → List Bool :=
  ![encodeWord x, graph, [], [], [], [], [], [], [], output]

theorem originalMemory_input (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalClean.Input t e (originalMemory (GraphTables.tableBits t) e.val output) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

theorem originalFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes originalView (originalMemory graph x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

theorem originalCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularOriginalClean.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = originalCoreInstruction q labels exit l)
    (t : GraphTables.Table) (e : Fin t.darts) (v i k o m : Nat)
    (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularOriginalClean.steps q t e
        (originalMemory (GraphTables.tableBits t) e.val output)]
      (some ⟨some (labels (.row (.lookup .seed))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor
          (output ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))
          [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedDivMod.residue q positive 0,
    (false, MachineCloudSelect.Phase.checking)))
  have run := MachineRegularOriginalClean.traceAt q id none
    (MachineRegularOriginalClean.instruction q id none) (fun _ => rfl) t e
    (originalMemory (GraphTables.tableBits t) e.val output)
    (originalMemory_input t e output) state none
  rw [originalMemory_update] at run
  have moved := MachineStateEquiv.trace (originalStateEquiv σ q)
    (MachineRegularOriginalClean.instruction q id none) _ _ _ run
  have placed := MachineCloudPadding.Placement.trace originalTapes originalView
    originalView_left originalView_right labels exit
    (coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] [])
    (MachineStateEquiv.program (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none)) program code _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, originalFrame] at placed
  convert placed using 1 <;> rfl

def dummyTapes : MachineRegularDummyRow.Tape → CoreTape := ![1, 24, 25, 9, 8, 26]

def dummyView : CoreTape → Option MachineRegularDummyRow.Tape :=
  ![none, some 0, none, none, none, none, none, none, some 4, some 3,
    none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, some 1, some 2, some 5]

theorem dummyView_left (k : MachineRegularDummyRow.Tape) :
    dummyView (dummyTapes k) = some k := by fin_cases k <;> rfl

theorem dummyView_right (j : CoreTape) (k : MachineRegularDummyRow.Tape)
    (h : dummyView j = some k) : dummyTapes k = j := by
  fin_cases j <;> simp [dummyView] at h
  all_goals subst k; rfl

def dummyCoreInstruction (q : Nat) (labels : MachineRegularDummyRow.Label → Λ)
    (exit : Option Λ) (l : MachineRegularDummyRow.Label) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  MachineCloudPadding.Placement.statement dummyTapes labels exit
    (MachineRegularDummyRow.instruction q id none l)

theorem dummyMemory_update (x : Nat) (output output' : List Bool) :
    Function.update (MachineRegularDummyRow.memory x output)
      (4 : MachineRegularDummyRow.Tape) output' = MachineRegularDummyRow.memory x output' := by
  funext j; fin_cases j <;> rfl

theorem dummyFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes dummyView (MachineRegularDummyRow.memory x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

theorem dummyCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularDummyRow.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = dummyCoreInstruction q labels exit l)
    (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularDummyRow.timeBound q x output.length]
      (some ⟨some (labels (.affine .seed)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor
          (output ++ MachineRegularDummyRow.emittedBits q x) [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  have run := MachineRegularDummyRow.traceAt q id none
    (MachineRegularDummyRow.instruction q id none) (fun _ => rfl) x
    (MachineRegularDummyRow.memory x output) (MachineRegularDummyRow.memory_input x output) state none
  rw [dummyMemory_update] at run
  have placed := MachineCloudPadding.Placement.trace dummyTapes dummyView
    dummyView_left dummyView_right labels exit
    (coreMemory graph x v i k o m rotor output [] [] [] [] [] [])
    (MachineRegularDummyRow.instruction q id none) program code _ _ _ run
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    dummyFrame] at placed
  have hs : MachineRegularDummyRow.steps q x output =
      MachineRegularDummyRow.timeBound q x output.length := MachineRegularDummyRow.steps_eq q x output
  change (advance (TM2.step program))^[MachineRegularDummyRow.steps q x output] _ = _ at placed
  rw [hs] at placed
  exact placed

inductive Label (q : Nat)
  | originalPort (l : PortLabel q)
  | dummyPort (l : PortLabel q)
  | original (l : MachineRegularOriginalClean.Label)
  | dummy (l : MachineRegularDummyRow.Label)
  deriving DecidableEq, Fintype

def originalEntry (q : Nat) (positive : 0 < q) : Label q :=
  .originalPort (⟨0, positive⟩, coreEntry q)

def dummyEntry (q : Nat) (positive : 0 < q) : Label q :=
  .dummyPort (⟨0, positive⟩, coreEntry q)

def instruction (q : Nat) (positive : 0 < q) (labels : Label q → Λ) (exit : Option Λ) :
    Label q → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q)
  | .originalPort l => portInstruction q positive (fun p => labels (.originalPort p))
      (some (labels (.original (.row (.lookup .seed))))) l
  | .dummyPort l => portInstruction q positive (fun p => labels (.dummyPort p))
      (some (labels (.dummy (.affine .seed)))) l
  | .original l => originalCoreInstruction q (fun s => labels (.original s)) exit l
  | .dummy l => dummyCoreInstruction q (fun s => labels (.dummy s)) exit l

def oldCloud (t : GraphTables.Table) (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    PaddedCloud t padding t.rows[e].tail := paddedOld t padding t.rows[e].tail ⟨e, rfl⟩

def originalRowSteps (q : Nat) (t : GraphTables.Table) (e : Fin t.darts) (outputLength : Nat) : Nat :=
  MachineRegularOriginalClean.steps q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate outputLength false))

theorem originalRowSteps_eq (q : Nat) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalClean.steps q t e (originalMemory (GraphTables.tableBits t) e.val output) =
      originalRowSteps q t e output.length := by
  unfold originalRowSteps MachineRegularOriginalClean.steps
  rw [MachineRegularOriginalClean.cleanupSteps_eq q t e _ (originalMemory_input t e output),
    MachineRegularOriginalClean.cleanupSteps_eq q t e _
      (originalMemory_input t e (List.replicate output.length false))]
  simp only [MachineRegularOriginalRow.steps, MachineRegularOriginalRow.rowSteps,
    originalMemory, Matrix.cons_val, List.length_replicate]

private theorem encodeWords_flatMap {A : Type*} (xs : List A) (words : A → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

private theorem encodeWords_pair (a b : Nat) (rest : List Nat) :
    encodeWords ([a, b] ++ rest) = encodeWord a ++ (encodeWord b ++ encodeWords rest) := rfl

theorem vertexBits_split (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    PreprocessingRegularWords.vertexBits t padding tables x.val =
      (List.ofFn (rowBits t padding tables v x)).flatten ++
        encodeWords (GraphTables.rowWords
          (PreprocessingRegularWords.actualRow t padding tables x.val (.inr ()))) := by
  unfold PreprocessingRegularWords.vertexBits PreprocessingRegularWords.vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  rfl

def originalSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) : Nat :=
  portSteps t padding tables t.rows[e].tail (oldCloud t padding e) outputLength q +
    originalRowSteps q t e (outputLength +
      (List.ofFn (rowBits t padding tables t.rows[e].tail (oldCloud t padding e))).flatten.length)

theorem originalTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[originalSteps t padding tables e output.length]
      (some ⟨some (labels (originalEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e)
          (output ++ PreprocessingRegularWords.originalVertexBits t padding tables e)⟩ := by
  let x := oldCloud t padding e
  let bits := (List.ofFn (rowBits t padding tables t.rows[e].tail x)).flatten
  have ports := portTrace q positive (fun l => labels (.originalPort l))
    (some (labels (.original (.row (.lookup .seed))))) program
    (fun l => code (.originalPort l)) t padding tables t.rows[e].tail x output ambient
  have inherited := originalCoreTrace q positive (fun l => labels (.original l)) exit program
    (fun l => code (.original l)) t e t.rows[e].tail.val
    (paddedCloudRank t padding t.rows[e].tail x).val (cloudSize t t.rows[e].tail)
    (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))) (output ++ bits) ambient
  rw [originalRowSteps_eq] at inherited
  change (advance (TM2.step program))^[originalRowSteps q t e (output ++ bits).length]
    (some ⟨some (labels (.original (.row (.lookup .seed)))), coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x (output ++ bits)⟩) =
    some ⟨exit, coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x
        ((output ++ bits) ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ at inherited
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e) := by
    have h := vertexBits_split t padding tables t.rows[e].tail x
    change PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inl e) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_original_words] at h
    exact h
  rw [hbits]
  simpa only [originalSteps, portEntry, dite_eq_left positive, originalEntry,
    List.length_append, List.append_assoc, x, bits] using total

def dummySteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) : Nat :=
  portSteps t padding tables v (paddedNew t padding v j) outputLength q +
    MachineRegularDummyRow.timeBound q (vertexOrder t padding (.inr ⟨v, j⟩)).val
      (outputLength + (List.ofFn (rowBits t padding tables v (paddedNew t padding v j))).flatten.length)

theorem dummyTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[dummySteps t padding tables v j output.length]
      (some ⟨some (labels (dummyEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j)
          (output ++ PreprocessingRegularWords.dummyVertexBits t padding tables v j)⟩ := by
  let x := paddedNew t padding v j
  let bits := (List.ofFn (rowBits t padding tables v x)).flatten
  have ports := portTrace q positive (fun l => labels (.dummyPort l))
    (some (labels (.dummy (.affine .seed)))) program
    (fun l => code (.dummyPort l)) t padding tables v x output ambient
  have inherited := dummyCoreTrace q positive (fun l => labels (.dummy l)) exit program
    (fun l => code (.dummy l)) (GraphTables.tableBits t) (vertexOrder t padding x.val).val v.val
    (paddedCloudRank t padding v x).val (cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) (output ++ bits) ambient
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ MachineRegularDummyRow.emittedBits q (vertexOrder t padding x.val).val := by
    have h := vertexBits_split t padding tables v x
    change PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inr ⟨v, j⟩) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_dummy_words] at h
    rw [encodeWords_pair] at h
    rw [show (vertexOrder t padding x.val).val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val from
      PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j]
    simpa only [MachineRegularDummyRow.emittedBits, MachineRegularDummyRow.reverseIndex,
      MachineDummyRows.rowBits, MachineDummyRows.trueBits, List.append_assoc] using h
  rw [hbits]
  simp only [dummySteps, portEntry, dite_eq_left positive, dummyEntry,
    List.length_append, List.append_assoc, x, bits] at total ⊢
  convert total using 1 <;> rfl

def rowSizeBound (q vertices : Nat) : Nat := vertices + vertices * (q + 1) + 8192

theorem rowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (rowBits t padding tables v x p).length ≤ rowSizeBound q (vertexCount t padding) :=
  GraphTables.rowBits_length_le _

theorem portBits_length_le {q : Nat} (bits : Fin q → List Bool) (bound : Nat)
    (hbits : ∀ p, (bits p).length ≤ bound) (k : Nat) :
    (portBits bits k).length ≤ k * bound := by
  induction k with
  | zero => simp only [portBits, List.length_nil, Nat.zero_mul, le_refl]
  | succ k ih =>
    rw [portBits, List.length_append]
    split_ifs with h
    · have hp := hbits ⟨k, h⟩
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih hp
    · simp only [List.length_nil, Nat.add_zero]
      exact ih.trans (Nat.mul_le_mul_right bound (by omega))

theorem allRowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    (List.ofFn (rowBits t padding tables v x)).flatten.length ≤
      q * rowSizeBound q (vertexCount t padding) := by
  rw [← portBits_all]
  exact portBits_length_le _ _ (rowBits_length_le t padding tables v x) q

def portTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  q * coreTimeBound q graphLength rotorLength x v i k o m
    (outputLength + q * rowSizeBound q vertices)

theorem portSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) (n : Nat) (hn : n ≤ q) :
    portSteps t padding tables v x outputLength n ≤
      n * coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
        (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
  induction n with
  | zero => simp only [portSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < q := by omega
    have first := ih (by omega)
    have second := coreSteps_le q positive t padding tables v x ⟨n, h⟩
      (outputLength + (portBits (rowBits t padding tables v x) n).length)
    have hlen := portBits_length_le (rowBits t padding tables v x)
      (rowSizeBound q (vertexCount t padding)) (rowBits_length_le t padding tables v x) n
    have hmul := Nat.mul_le_mul_right (rowSizeBound q (vertexCount t padding)) (Nat.le_of_lt h)
    have hcost : coreSteps t padding tables v x ⟨n, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) n).length) ≤
        coreTimeBound q (GraphTables.tableBits t).length
          (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
          (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
          (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
          (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
      unfold coreTimeBound at second ⊢
      omega
    rw [portSteps, dite_eq_left h, Nat.succ_mul]
    exact Nat.add_le_add first hcost

def originalTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularOriginalClean.timeBound q graphLength
      (outputLength + q * rowSizeBound q vertices)

def dummyTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularDummyRow.timeBound q x (outputLength + q * rowSizeBound q vertices)

theorem originalSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) :
    originalSteps t padding tables e outputLength ≤
      originalTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))).length
        e.val t.rows[e].tail.val (paddedCloudRank t padding t.rows[e].tail (oldCloud t padding e)).val
        (cloudSize t t.rows[e].tail) (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val)
        t.darts outputLength (vertexCount t padding) := by
  let v := t.rows[e].tail
  let x := oldCloud t padding e
  let extra := (List.ofFn (rowBits t padding tables v x)).flatten.length
  have hp := portSteps_le q positive t padding tables v x outputLength q le_rfl
  have hi := MachineRegularOriginalClean.steps_le q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate (outputLength + extra) false))
    (originalMemory_input t e (List.replicate (outputLength + extra) false))
  have hl := allRowBits_length_le t padding tables v x
  change originalRowSteps q t e (outputLength + extra) ≤
    MachineRegularOriginalClean.timeBound q (GraphTables.tableBits t).length
      (List.replicate (outputLength + extra) false).length at hi
  rw [List.length_replicate] at hi
  change portSteps t padding tables v x outputLength q +
    originalRowSteps q t e (outputLength + extra) ≤ _
  unfold originalTimeBound portTimeBound MachineRegularOriginalClean.timeBound at *
  have hx : (vertexOrder t padding x.val).val = e.val := rfl
  rw [hx] at hp
  dsimp only [v, x, extra] at *
  omega

theorem dummySteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) :
    dummySteps t padding tables v j outputLength ≤
      dummyTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding (.inr ⟨v, j⟩)).val v.val
        (paddedCloudRank t padding v (paddedNew t padding v j)).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val)
        t.darts outputLength (vertexCount t padding) := by
  have hp := portSteps_le q positive t padding tables v (paddedNew t padding v j) outputLength q le_rfl
  have hl := allRowBits_length_le t padding tables v (paddedNew t padding v j)
  unfold dummySteps dummyTimeBound portTimeBound MachineRegularDummyRow.timeBound
  have hx : (paddedNew t padding v j).val = Sum.inr ⟨v, j⟩ := rfl
  rw [hx] at hp
  omega

def originalMachine (q : Nat) (positive : 0 < q) : FinTM2 where
  K := CoreTape
  k₀ := 0
  k₁ := 8
  Γ _ := Bool
  Λ := Label q
  main := originalEntry q positive
  σ := CoreState Unit q
  initialState := coreInitialState q positive ()
  m := instruction q positive id none

def dummyMachine (q : Nat) (positive : 0 < q) : FinTM2 where
  K := CoreTape
  k₀ := 0
  k₁ := 8
  Γ _ := Bool
  Λ := Label q
  main := dummyEntry q positive
  σ := CoreState Unit q
  initialState := coreInitialState q positive ()
  m := instruction q positive id none

def originalMachineInTime (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (output : List Bool) :
    StateTransition.EvalsToInTime (originalMachine q positive).step
      ⟨some (originalEntry q positive), coreInitialState q positive (),
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e) output⟩
      (some ⟨none, coreInitialState q positive (),
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e)
          (output ++ PreprocessingRegularWords.originalVertexBits t padding tables e)⟩)
      (originalTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))).length
        e.val t.rows[e].tail.val (paddedCloudRank t padding t.rows[e].tail (oldCloud t padding e)).val
        (cloudSize t t.rows[e].tail) (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val)
        t.darts output.length (vertexCount t padding)) where
  steps := originalSteps t padding tables e output.length
  evals_in_steps := originalTraceAt q positive id none (instruction q positive id none)
    (fun _ => rfl) t padding tables e output ()
  steps_le_m := originalSteps_le q positive t padding tables e output.length

def dummyMachineInTime (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (output : List Bool) :
    StateTransition.EvalsToInTime (dummyMachine q positive).step
      ⟨some (dummyEntry q positive), coreInitialState q positive (),
        coreInputTapes t padding tables v (paddedNew t padding v j) output⟩
      (some ⟨none, coreInitialState q positive (),
        coreInputTapes t padding tables v (paddedNew t padding v j)
          (output ++ PreprocessingRegularWords.dummyVertexBits t padding tables v j)⟩)
      (dummyTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding (.inr ⟨v, j⟩)).val v.val
        (paddedCloudRank t padding v (paddedNew t padding v j)).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val)
        t.darts output.length (vertexCount t padding)) where
  steps := dummySteps t padding tables v j output.length
  evals_in_steps := dummyTraceAt q positive id none (instruction q positive id none)
    (fun _ => rfl) t padding tables v j output ()
  steps_le_m := dummySteps_le q positive t padding tables v j output.length

end BinPackingGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
