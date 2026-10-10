import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularTableRuntime
import OAI.Combinatorics.IndependentSets.Machines.MachinePaddingCertificate

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open IndependentSetsGames.Foundations.PCP
open MachineCloudPadding

inductive Tape
  | original | output | vertex | edge | power | level | fuel | relation
  | scratch | work | saved | product | rowWork | rowSpare
  deriving DecidableEq

instance : Fintype Tape where
  elems := {.original, .output, .vertex, .edge, .power, .level, .fuel, .relation, .scratch, .work,
    .saved, .product, .rowWork, .rowSpare}
  complete value := by cases value <;> simp

inductive Label (d : Nat)
  | splitCode (l : MachineTableSplit.Label)
  | powerCode (l : MachineCeilingPower.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | copyFirst | copySecond | subtractCode (l : MachineCloudPadding.Label)
  | rowsCode (l : MachinePaddingRows.Label d)
  | cleanVertex | cleanEdge | cleanPower | cleanRelation | cleanFuel
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (input output vertex edge power level fuel relation : List Bool) : Tape → List Bool
  | .original => input
  | .output => output
  | .vertex => vertex
  | .edge => edge
  | .power => power
  | .level => level
  | .fuel => fuel
  | .relation => relation
  | _ => []

@[simp] theorem update_output (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .output x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_vertex (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .vertex x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_edge (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .edge x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_relation (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .relation x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

def splitTape : MachineTableSplit.Tape → Tape := ![.original, .output, .scratch, .vertex, .edge]
def splitView : Tape → Option MachineTableSplit.Tape
  | .original => some 0
  | .output => some 1
  | .scratch => some 2
  | .vertex => some 3
  | .edge => some 4
  | _ => none

theorem splitView_left (k : MachineTableSplit.Tape) : splitView (splitTape k) = some k := by
  fin_cases k <;> rfl
theorem splitView_right (j : Tape) (k : MachineTableSplit.Tape)
    (h : splitView j = some k) : splitTape k = j := by
  cases j <;> fin_cases k <;> simp_all [splitView, splitTape]

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .vertex
  | .work => .work
  | .power => .power
  | .saved => .saved
  | .level => .level
  | .fuel => .fuel
  | .spare => .scratch
  | .product => .product
def powerView : Tape → Option MachineCeilingPower.Tape
  | .vertex => some .input
  | .work => some .work
  | .power => some .power
  | .saved => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .scratch => some .spare
  | .product => some .product
  | _ => none

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

def subtractTape : MachineCloudPadding.Tape → Tape
  | .table => .original
  | .query => .output
  | .count => .vertex
  | .work => .work
  | .scratch => .saved
  | .spare => .scratch
  | .power => .fuel
  | .level => .level
  | .fuel => .product
  | .product => .rowSpare
def subtractView : Tape → Option MachineCloudPadding.Tape
  | .original => some .table
  | .output => some .query
  | .vertex => some .count
  | .work => some .work
  | .saved => some .scratch
  | .scratch => some .spare
  | .fuel => some .power
  | .level => some .level
  | .product => some .fuel
  | .rowSpare => some .product
  | _ => none

theorem subtractView_left (k : MachineCloudPadding.Tape) :
    subtractView (subtractTape k) = some k := by cases k <;> rfl
theorem subtractView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : subtractView j = some k) : subtractTape k = j := by
  cases j <;> cases k <;> simp_all [subtractView, subtractTape]

def rowTape : MachinePaddingRows.Tape → Tape
  | .inl k => (![.vertex, .edge, .relation, .rowWork, .output, .rowSpare] : Fin 6 → Tape) k
  | .inr _ => .fuel
def rowView : Tape → Option MachinePaddingRows.Tape
  | .vertex => some (.inl 0)
  | .edge => some (.inl 1)
  | .relation => some (.inl 2)
  | .rowWork => some (.inl 3)
  | .output => some (.inl 4)
  | .rowSpare => some (.inl 5)
  | .fuel => some (.inr ())
  | _ => none

theorem rowView_left (k : MachinePaddingRows.Tape) : rowView (rowTape k) = some k := by
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl
theorem rowView_right (j : Tape) (k : MachinePaddingRows.Tape)
    (h : rowView j = some k) : rowTape k = j := by
  rcases k with k | k
  · cases j <;> fin_cases k <;> simp_all [rowView, rowTape]
  · cases k; cases j <;> simp_all [rowView, rowTape]

theorem rowAlphabet_eq : MachinePaddingRows.Alphabet = (fun _ : MachinePaddingRows.Tape => Bool) := by
  funext k; cases k <;> rfl

def rowStateEquiv (σ : Type) : (MachinePaddingRows.State × (σ × Bool)) ≃ State σ where
  toFun x := (x.2, x.1.1.2)
  invFun x := ((((), x.2), ()), x.1)
  left_inv := by rintro ⟨⟨⟨⟨⟩, r⟩, ⟨⟩⟩, a⟩; rfl
  right_inv := by rintro ⟨a, r⟩; rfl

def rowProgram {σ : Type} (d : Nat) (hd : 0 < d) :
    MachinePaddingRows.Label d →
      TM2.Stmt (fun _ : MachinePaddingRows.Tape => Bool) (MachinePaddingRows.Label d) (State σ) :=
  MachineStateEquiv.program (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))

def program {σ : Type} (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) (State σ)
  | .splitCode l => Placement.statement splitTape Label.splitCode (some (.powerCode .init))
      (MachineTableSplit.program l)
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .dartSeed)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .power .scratch .output d .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .power .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .vertexRestore (some .copyFirst)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .power .scratch id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .scratch .power .fuel false .copySecond (some (.subtractCode .subtract))
  | .subtractCode l => Placement.statement subtractTape Label.subtractCode
      (some (.rowsCode (.inr .initialize))) (MachineCloudPadding.program l)
  | .rowsCode l => Placement.statement rowTape Label.rowsCode (some .cleanVertex) (rowProgram d hd l)
  | .cleanVertex => MachineDrain.drain .vertex .cleanVertex (some .cleanEdge)
  | .cleanEdge => MachineDrain.drain .edge .cleanEdge (some .cleanPower)
  | .cleanPower => MachineDrain.drain .power .cleanPower (some .cleanRelation)
  | .cleanRelation => MachineDrain.drain .relation .cleanRelation (some .cleanFuel)
  | .cleanFuel => MachineDrain.drain .fuel .cleanFuel none

private theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

theorem tableBits_split {n d : Nat} (t : PortTables.Table n d) :
    PortTables.tableBits t = encodeWords [n, n * d] ++ PreprocessingPaddingWords.rowsBits t := by
  change encodeWords (PortTables.tableWords t) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  rfl

theorem splitInitialTapes (word : List Bool) :
    Placement.tapes splitView (MachineTableSplit.initialTapes word) (fun _ => []) =
      memory word [] [] [] [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.initialTapes,
    MachineTableSplit.tapes, memory]

theorem splitResultTapes (n e : Nat) (rows : List Bool) :
    Placement.tapes splitView (MachineTableSplit.resultTapes n e rows) (fun _ => []) =
      memory (encodeWords [n, e] ++ rows) rows (encodeWord n) (encodeWord e) [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.resultTapes,
    MachineTableSplit.tapes, memory]

theorem splitTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineTableSplit.exactSteps n (n * d)
      (PreprocessingPaddingWords.rowsBits t)]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory (PortTables.tableBits t) (PreprocessingPaddingWords.rowsBits t)
          (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ := by
  have h := Placement.trace splitTape splitView splitView_left splitView_right
    (Label.splitCode (d := d)) (some (.powerCode .init)) (fun _ => [])
    (MachineTableSplit.program (σ := σ × Bool)) (program d hd) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n (n * d) (PreprocessingPaddingWords.rowsBits t)
      (ambient, false) register)
  simpa only [Placement.configuration, Placement.label, splitInitialTapes, splitResultTapes,
    ← tableBits_split] using h

theorem powerTapes (input output vertex edge power level : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory vertex [] power [] level [] [] [])
      (memory input output [] edge [] [] [] []) = memory input output vertex edge power level [] [] := by
  funext k; cases k <;> rfl

theorem powerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge : List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineCeilingPower.totalTime ExpanderFamily.growth n]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory input output (encodeWord n) edge [] [] [] []⟩) =
      some ⟨some .dartSeed, ((ambient, false), none),
        memory input output (encodeWord n) edge (encodeWord (PreprocessingLevels.paddedSize n))
          (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    (Label.powerCode (d := d)) (some .dartSeed) (memory input output [] edge [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) (program d hd)
    (fun _ => rfl) _ _ _ (MachineCeilingPower.paddingTrace n ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes] using h

theorem affineTapes (input output vertex edge power level fuel relation : List Bool) :
    MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output
      (memory input output vertex edge power level fuel relation) power [] output =
      memory input output vertex edge power level fuel relation := by
  funext k
  cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, memory]

theorem affineOutputTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (coefficient : Nat) (seed scan restore : Label d) (exit : Option (Label d))
    (atSeed : program (σ := σ) d hd seed = MachineUnaryAffineAt.seed (σ := σ × Bool) .output 0 scan)
    (atScan : program (σ := σ) d hd scan = MachineUnaryAffineAt.scan (σ := σ × Bool) .power .scratch .output
      coefficient scan restore)
    (atRestore : program (σ := σ) d hd restore = Reduction.MachineTransfer.loopAt (σ := σ × Bool)
      .scratch .power id false restore exit)
    (input output vertex edge level fuel relation : List Bool) (m : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[1 + 2 * (m + 1)]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨exit, ((ambient, false), none),
        memory input (encodeWord (coefficient * m) ++ output) vertex edge
          (encodeWord m) level fuel relation⟩ := by
  have hs : (advance (TM2.step (program d hd)))^[1]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨some scan, ((ambient, false), register),
        memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation⟩ := by
    change some (TM2.stepAux (program d hd seed) _ _) = _
    rw [atSeed]
    simp [MachineUnaryAffineAt.seed, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, encodeWord, memory]
  let base := memory input output vertex edge (encodeWord m) level fuel relation
  have ht := MachineUnaryAffineAt.affineTrace Tape.power Tape.scratch Tape.output
    (by decide) (by decide) (by decide) coefficient scan restore exit (program d hd)
    atScan atRestore base m 0 [] output (ambient, false) register
  have hstart : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord 0 ++ output) =
      memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  have hfinish : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord (coefficient * m + 0) ++ output) =
      memory input (encodeWord (coefficient * m) ++ output) vertex edge
        (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  rw [hstart, hfinish] at ht
  exact appendTrace _ hs ht

theorem headersTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[4 * (m + 1) + 2]
      (some ⟨some .dartSeed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory input (encodeWords [m, m * d] ++ output) vertex edge (encodeWord m) level [] []⟩ := by
  have h₁ := affineOutputTrace d hd d .dartSeed .dartScan .dartRestore (some .vertexSeed)
    rfl rfl rfl input output vertex edge level [] [] m ambient register
  have h₂ := affineOutputTrace d hd 1 .vertexSeed .vertexScan .vertexRestore (some .copyFirst)
    rfl rfl rfl input (encodeWord (d * m) ++ output) vertex edge level [] [] m ambient none
  have h := appendTrace _ h₁ h₂
  simpa only [Nat.one_mul, Nat.mul_comm d m, encodeWords, List.append_nil, List.append_assoc,
    show (1 + 2 * (m + 1)) + (1 + 2 * (m + 1)) = 4 * (m + 1) + 2 by omega] using h

theorem copyPowerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * (m + 2)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some (.subtractCode .subtract), ((ambient, false), none),
        memory input output vertex edge (encodeWord m) level (encodeWord m) []⟩ := by
  have h := MachineCopy.copyTrace Tape.power Tape.fuel Tape.scratch
    (by decide) (by decide) (by decide) false (Label.copyFirst (d := d)) .copySecond
    (some (.subtractCode .subtract)) (program d hd) rfl rfl
    (memory input output vertex edge (encodeWord m) level [] []) rfl (ambient, false) register
  simpa only [memory, encodeWord_length, List.append_nil, update_fuel] using h

theorem subtractTapes (input output vertex edge power level fuel : List Bool) :
    Placement.tapes subtractView
      (MachineCloudPadding.memory input output vertex [] [] [] fuel level [] [])
      (memory [] [] [] edge power [] [] []) =
      memory input output vertex edge power level fuel [] := by
  funext k; cases k <;> rfl

theorem subtractTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge power level : List Bool) (n m : Nat) (hnm : n ≤ m)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * n + 2]
      (some ⟨some (.subtractCode .subtract), ((ambient, false), register),
        memory input output (encodeWord n) edge power level (encodeWord m) []⟩) =
      some ⟨some (.rowsCode (.inr .initialize)), ((ambient, false), none),
        memory input output (encodeWord n) edge power level (encodeWord (m - n)) []⟩ := by
  have h := Placement.trace subtractTape subtractView subtractView_left subtractView_right
    (Label.subtractCode (d := d)) (some (.rowsCode (.inr .initialize)))
    (memory [] [] [] edge power [] [] [])
    (MachineCloudPadding.program (σ := σ)) (program d hd) (fun _ => rfl) _ _ _
    (MachineCloudPadding.subtractTrace input output level n m hnm ambient register)
  simpa only [Placement.configuration, Placement.label, subtractTapes] using h

def rowBoolTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachinePaddingRows.Tape → List Bool
  | .inl k => base (.inl k)
  | .inr k => base (.inr k)

private theorem transport_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem rowCastTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachineAlphabetTransport.tapes rowAlphabet_eq base = rowBoolTapes base := by
  funext k
  rw [transport_tapes_apply]
  cases k <;> rfl

theorem rowInitialTapes (input power level output : List Bool) (v e fuel : Nat) :
    Placement.tapes rowView (rowBoolTapes (MachinePaddingRows.initialTapes v e fuel output))
      (memory input [] [] [] power level [] []) =
      memory input output (encodeWord v) (encodeWord e) power level (encodeWord fuel) [] := by
  funext k
  cases k <;> rfl

theorem rowFinalTapes (input power level output : List Bool) (v e fuel : Nat) :
    Placement.tapes rowView (rowBoolTapes (MachinePaddingRows.tapes v e fuel output))
      (memory input [] [] [] power level [] []) =
      memory input output (encodeWord v) (encodeWord e) power level (encodeWord fuel)
        MachineDummyRows.trueBits := by
  funext k
  cases k <;> rfl

def rowTime {n d m : Nat} (t : PortTables.Table n d) : Nat :=
  MachinePaddingRows.steps d n (n * d) (MachinePaddingTable.initialOutput (m := m) t) (m - n) + 1

private theorem frameTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ) (n : Nat)
    (a b : TM2.Cfg Γ Λ σ) (run : (advance (TM2.step source))^[n] (some a) = some b) :
    (advance (TM2.step (MachineStateFrame.frameProgram source)))^[n]
      (some (MachineStateFrame.frameConfiguration ambient a)) =
      some (MachineStateFrame.frameConfiguration ambient b) := by
  have h := MachineStateFrame.frame_iterate source ambient n (some a)
  simpa only [Option.map_some, run] using h

theorem rowsTrace {σ : Type} {n d m : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (hnm : n ≤ m) (input power level : List Bool) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[rowTime (m := m) t]
      (some ⟨some (.rowsCode (.inr .initialize)), ((ambient, false), none),
        memory input (MachinePaddingTable.initialOutput (m := m) t)
          (encodeWord n) (encodeWord (n * d)) power level (encodeWord (m - n)) []⟩) =
      some ⟨some .cleanVertex, ((ambient, false), none),
        memory input (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))
          (encodeWord m) (encodeWord (m * d)) power level (encodeWord 0)
          MachineDummyRows.trueBits⟩ := by
  have hraw := (MachinePaddingTable.execution t hnm hd).evals_in_steps
  change (advance (TM2.step (MachinePaddingRows.program d hd)))^[rowTime (m := m) t]
    (some ⟨some (.inr .initialize), (((), none), ()),
      MachinePaddingRows.initialTapes n (n * d) (m - n)
        (MachinePaddingTable.initialOutput (m := m) t)⟩) =
    some (MachinePaddingRows.cfg d none m (m * d) 0
      (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))) at hraw
  have hb := MachineAlphabetTransport.successfulTrace rowAlphabet_eq
    (MachinePaddingRows.program d hd) _ _ _ hraw
  have hf := frameTrace
    (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd))
    (ambient, false) _ _ _ hb
  have hs := MachineStateEquiv.trace (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))
    _ _ _ hf
  have hp := Placement.trace rowTape rowView rowView_left rowView_right
    (Label.rowsCode (d := d)) (some .cleanVertex) (memory input [] [] [] power level [] [])
    (rowProgram d hd (σ := σ)) (program d hd) (fun _ => rfl) _ _ _ hs
  simpa only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    MachineStateFrame.frameConfiguration, MachineAlphabetTransport.configuration_mk,
    rowCastTapes, MachinePaddingRows.cfg, rowStateEquiv, Equiv.coe_fn_mk,
    rowInitialTapes, rowFinalTapes] using hp

def cleanupTime (d m : Nat) : Nat := 2 * m + m * d + 8201

theorem cleanupTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output level : List Bool) (m : Nat) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[cleanupTime d m]
      (some ⟨some .cleanVertex, ((ambient, false), none),
        memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
          (encodeWord 0) MachineDummyRows.trueBits⟩) =
      some ⟨none, ((ambient, false), none), memory input output [] [] [] level [] []⟩ := by
  have h₁ := (MachineDrain.drainInTime Tape.vertex (Label.cleanVertex (d := d)) (some .cleanEdge)
    (program d hd) rfl
    (memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₂ := (MachineDrain.drainInTime Tape.edge (Label.cleanEdge (d := d)) (some .cleanPower)
    (program d hd) rfl
    (memory input output [] (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₃ := (MachineDrain.drainInTime Tape.power (Label.cleanPower (d := d)) (some .cleanRelation)
    (program d hd) rfl
    (memory input output [] [] (encodeWord m) level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₄ := (MachineDrain.drainInTime Tape.relation (Label.cleanRelation (d := d)) (some .cleanFuel)
    (program d hd) rfl
    (memory input output [] [] [] level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₅ := (MachineDrain.drainInTime Tape.fuel (Label.cleanFuel (d := d)) none
    (program d hd) rfl (memory input output [] [] [] level (encodeWord 0) [])
    (ambient, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, memory, encodeWord_length, MachineDummyRows.trueBits_length,
    update_vertex, update_edge, update_power, update_relation, update_fuel] at h₁ h₂ h₃ h₄ h₅
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅
  have ht : cleanupTime d m = (((m + 2 + (m * d + 2)) + (m + 2)) + 8193) + 2 := by
    unfold cleanupTime
    omega
  rw [ht]
  exact h

def otherTime {n d : Nat} (t : PortTables.Table n d) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (PreprocessingPaddingWords.rowsBits t) +
    MachineCeilingPower.totalTime ExpanderFamily.growth n +
    (4 * (PreprocessingLevels.paddedSize n + 1) + 2) +
    (2 * (PreprocessingLevels.paddedSize n + 2)) + (2 * n + 2) +
    cleanupTime d (PreprocessingLevels.paddedSize n)

def totalTime {n d : Nat} (t : PortTables.Table n d) : Nat :=
  otherTime t + rowTime (m := PreprocessingLevels.paddedSize n) t

theorem vertexPaddingTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[totalTime t]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  let m := PreprocessingLevels.paddedSize n
  let level := encodeWord (PreprocessingLevels.boundedLevel n)
  let input := PortTables.tableBits t
  let rows := PreprocessingPaddingWords.rowsBits t
  let initialOutput := MachinePaddingTable.initialOutput (m := m) t
  have h₁ := splitTrace hd t ambient register
  have h₂ := powerTrace d hd input rows (encodeWord (n * d)) n ambient none
  have h₃ := headersTrace d hd input rows (encodeWord n) (encodeWord (n * d)) level m ambient none
  have h₄ := copyPowerTrace d hd input initialOutput (encodeWord n) (encodeWord (n * d))
    level m ambient none
  have h₅ := subtractTrace d hd input initialOutput (encodeWord (n * d)) (encodeWord m)
    level n m (PreprocessingLevels.le_paddedSize n) ambient none
  have h₆ := rowsTrace hd t (PreprocessingLevels.le_paddedSize n) input (encodeWord m) level ambient
  have h₇ := cleanupTrace d hd input
    (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
    level m ambient
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _
    (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅) h₆) h₇
  have ht : totalTime t =
      (((((MachineTableSplit.exactSteps n (n * d) rows +
        MachineCeilingPower.totalTime ExpanderFamily.growth n) + (4 * (m + 1) + 2)) +
        (2 * (m + 2))) + (2 * n + 2)) + rowTime (m := m) t) + cleanupTime d m := by
    dsimp only [totalTime, otherTime, m, rows]
    omega
  rw [ht]
  exact h

theorem rows_length_le {n d : Nat} (t : PortTables.Table n d) :
    (PreprocessingPaddingWords.rowsBits t).length ≤ (PortTables.tableBits t).length := by
  rw [tableBits_split, List.length_append]
  omega

theorem darts_length_le {n d : Nat} (t : PortTables.Table n d) :
    n * d ≤ (PortTables.tableBits t).length :=
  GraphTables.darts_le_tableBits_length (PortTables.graphTable t)

theorem power_length_bound {n d : Nat} (t : PortTables.Table n d) :
    PreprocessingLevels.paddedSize n ≤ ExpanderFamily.growth * ((PortTables.tableBits t).length + 1) :=
  (MachineCeilingPower.paddingOutput_bounds n).2.2.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (PortTables.vertices_le_tableBits_length t) 1))

theorem initialOutput_length {n d m : Nat} (t : PortTables.Table n d) :
    (MachinePaddingTable.initialOutput (m := m) t).length =
      m + m * d + 2 + (PreprocessingPaddingWords.rowsBits t).length := by
  simp only [MachinePaddingTable.initialOutput, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

def intermediateCoefficient (d : Nat) : Nat := (d + 2) * ExpanderFamily.growth + 8

noncomputable def intermediatePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (intermediateCoefficient d) * (Polynomial.X + 1)

theorem intermediate_bound {n d : Nat} (t : PortTables.Table n d) :
    MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
      (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t) ≤
      (intermediatePolynomial d).eval (PortTables.tableBits t).length := by
  have hn := PortTables.vertices_le_tableBits_length t
  have he := darts_length_le t
  have hr := rows_length_le t
  have hm := power_length_bound t
  have hs := Nat.sub_le (PreprocessingLevels.paddedSize n) n
  have hmul := Nat.mul_le_mul_left (d + 2) hm
  simp only [MachinePaddingBounds.inputSize, encodeWord_length, initialOutput_length,
    intermediatePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, intermediateCoefficient]
  nlinarith

noncomputable def otherPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * (Polynomial.X + 1) ^ 2 +
    Polynomial.C ((d + 8) * ExpanderFamily.growth + 24) * (Polynomial.X + 1) + 8222

theorem otherTime_le {n d : Nat} (t : PortTables.Table n d) :
    otherTime t ≤ (otherPolynomial d).eval (PortTables.tableBits t).length := by
  have hs := MachineTableSplit.exactSteps_le n (n * d) (PreprocessingPaddingWords.rowsBits t)
  rw [← tableBits_split, MachineTableSplit.timePolynomial_eval] at hs
  have hc := MachineCeilingPower.totalTime_le ExpanderFamily.growth n
  have hn := PortTables.vertices_le_tableBits_length t
  have hm := power_length_bound t
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2)
  have hmul := Nat.mul_le_mul_left (d + 8) hm
  simp only [otherPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold otherTime cleanupTime
  unfold MachineCeilingPower.timeBound at hc
  nlinarith

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  otherPolynomial d + (MachinePaddingCertificate.timePolynomial d).comp (intermediatePolynomial d)

theorem totalTime_le {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    totalTime t ≤ (timePolynomial d).eval (PortTables.tableBits t).length := by
  have hrow := (MachinePaddingTable.execution t (PreprocessingLevels.le_paddedSize n) hd).steps_le_m
  change rowTime (m := PreprocessingLevels.paddedSize n) t ≤
    (MachinePaddingCertificate.timePolynomial d).eval
      (MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
        (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t)) at hrow
  have hmono := natPolynomial_eval_mono (MachinePaddingCertificate.timePolynomial d) (intermediate_bound t)
  have h := Nat.add_le_add (otherTime_le t) (hrow.trans hmono)
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp] using h

def vertexPaddingInTime {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program d hd))
      ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) where
  steps := totalTime t
  evals_in_steps := vertexPaddingTrace hd t ambient register
  steps_le_m := totalTime_le hd t

def machine (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .original
  k₁ := .output
  Γ := Alphabet
  Λ := Label d
  main := .splitCode .copyFirst
  σ := State Unit
  initialState := (((), false), none)
  m := program d hd

theorem alphabet_finite (d : Nat) (hd : 0 < d) : ∀ k, Finite ((machine d hd).Γ k) := by
  intro k
  exact inferInstanceAs (Finite Bool)

end IndependentSetsGames.Foundations.Complexity.MachineVertexPadding

end OAI
