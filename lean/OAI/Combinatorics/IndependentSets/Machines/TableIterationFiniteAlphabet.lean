import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineFiniteAlphabet
import OAI.Combinatorics.IndependentSets.Machines.FinalCNFComputation

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem initial : FiniteAlphabet MachineRawInitialTable.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem counter : FiniteAlphabet MachineTableIteration.counterCertificate.tm := by
  intro k
  change Finite Bool
  infer_instance

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem counted : FiniteAlphabet (MachineTableIteration.countedCertificate H body).tm :=
  repeat_machine body.tm body.inputAlphabet body.outputAlphabet finiteBody

theorem iteration : FiniteAlphabet (MachineTableIteration.computableInPolyTime H body).tm :=
  composeBits MachineTableIteration.counterCertificate
    (MachineTableIteration.countedCertificate H body) counter (counted H body finiteBody)

theorem table : FiniteAlphabet (MachineTableIteration.tableCertificate H body).tm :=
  composeBits MachineTableIteration.initialCertificate
    (MachineTableIteration.computableInPolyTime H body) initial (iteration H body finiteBody)

theorem gapMap : FiniteAlphabet (MachineTableIteration.gapMapCertificate H body).tm :=
  composeBits (MachineTableIteration.tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime (table H body finiteBody) finalCNF

end IndependentSetsGames.Foundations.Complexity.TableIterationFiniteAlphabet

namespace IndependentSetsCut.CounterMachine
open Turing

inductive Tape (R : Type) where
  | input | backup | output | reg (r : R)
  deriving DecidableEq, Fintype

inductive Instruction (R L : Type) where
  | inc (r : R) (next : L)
  | dec (r : R) (positive zero : L)
  | test (r : R) (zero positive : L)
  | read (one zero empty : L)
  | back (nonempty empty : L)
  | write (b : Bool) (next : L)
  | discard (next : L)
  | jump (next : L)
  | halt

structure Data (R : Type) where
  reg : R → ℕ
  input : List Bool
  backup : List Bool
  output : List Bool

structure Configuration (R L : Type) extends Data R where
  label : Option L

variable {R L : Type} [DecidableEq R]

def Instruction.execute (i : Instruction R L) (d : Data R) : Configuration R L :=
  match i with
  | .inc r next => ⟨{ d with reg := Function.update d.reg r (d.reg r + 1) }, some next⟩
  | .dec r positive zero =>
    ⟨{ d with reg := Function.update d.reg r (d.reg r - 1) },
      some (if d.reg r = 0 then zero else positive)⟩
  | .test r zero positive => ⟨d, some (if d.reg r = 0 then zero else positive)⟩
  | .read one zero empty =>
    ⟨{ d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }, some (match d.input with
      | [] => empty | true :: _ => one | false :: _ => zero)⟩
  | .back nonempty empty =>
    ⟨{ d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail },
      some (if d.backup = [] then empty else nonempty)⟩
  | .write b next => ⟨{ d with output := b :: d.output }, some next⟩
  | .discard next => ⟨{d with input := d.input.tail}, some next⟩
  | .jump next => ⟨d, some next⟩
  | .halt => ⟨d, none⟩

def step (p : L → Instruction R L) (c : Configuration R L) : Option (Configuration R L) :=
  c.label.map (fun l => (p l).execute c.toData)

def tapes (d : Data R) : Tape R → List Bool
  | .input => d.input
  | .backup => d.backup
  | .output => d.output
  | .reg r => List.replicate (d.reg r) true

def embed (c : Configuration R L) : TM2.Cfg (fun _ : Tape R => Bool) L (Option Bool) :=
  ⟨c.label, none, tapes c.toData⟩

def goto (l : L) : TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))

def Instruction.code : Instruction R L → TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool)
  | .inc r next => .push (.reg r) (fun _ => true) (goto next)
  | .dec r positive zero => .pop (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .test r zero positive => .peek (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .read one zero empty => .pop .input (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .backup (fun b => b.getD false)
          (.branch (fun b => b.getD false) (goto one) (goto zero))) (goto empty))
  | .back nonempty empty => .pop .backup (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .input (fun b => b.getD false) (goto nonempty)) (goto empty))
  | .write b next => .push .output (fun _ => b) (goto next)
  | .discard next => .pop .input (fun _ _ => none) (goto next)
  | .jump next => goto next
  | .halt => .halt

 theorem tapes_inc (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r + 1) } =
      Function.update (tapes d) (.reg r) (true :: tapes d (.reg r)) := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h, List.replicate_succ]

 theorem tapes_dec (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r - 1) } =
      Function.update (tapes d) (.reg r) (tapes d (.reg r)).tail := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h]

 theorem tapes_read (d : Data R) :
    tapes { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup } =
      Function.update (Function.update (tapes d) .input d.input.tail) .backup
        (d.input.take 1 ++ d.backup) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_back (d : Data R) :
    tapes { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail } =
      Function.update (Function.update (tapes d) .backup d.backup.tail) .input
        (d.backup.take 1 ++ d.input) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_write (d : Data R) (b : Bool) :
    tapes { d with output := b :: d.output } =
      Function.update (tapes d) .output (b :: d.output) := by
  funext k; cases k <;> simp [tapes]

 theorem instruction_simulation (i : Instruction R L) (d : Data R) :
    TM2.stepAux i.code none (tapes d) = embed (i.execute d) := by
  cases i with
  | inc r next => simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_inc]
  | dec r pos zero =>
    cases h : d.reg r with
    | zero =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      simpa [h, tapes] using (tapes_dec d r).symm
    | succ n =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed,
        tapes, h, List.replicate_succ]
      simpa [h, tapes] using (tapes_dec d r).symm
  | test r zero pos =>
    cases h : d.reg r <;>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h, List.replicate_succ]
  | read one zero empty =>
    cases h : d.input with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_read d).symm
  | back nonempty empty =>
    cases h : d.backup with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_back d).symm
  | write b next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_write, tapes]
  | discard next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed]
    funext k; cases k <;> simp [tapes]
  | jump next => rfl
  | halt => rfl

 theorem step_simulation (p : L → Instruction R L) (c : Configuration R L) :
    TM2.step (fun l => (p l).code) (embed c) = (step p c).map embed := by
  cases c with
  | mk d l =>
    cases l with
    | none => rfl
    | some l => simpa [TM2.step, step, embed] using congrArg some (instruction_simulation (p l) d)

def machine [Fintype R] [Fintype L] (p : L → Instruction R L) (main : L) : FinTM2 where
  K := Tape R
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := L
  main := main
  σ := Option Bool
  initialState := none
  m l := (p l).code

 theorem finite_tape_alphabet [Fintype R] [Fintype L]
    (p : L → Instruction R L) (main : L) (k : (machine p main).K) :
    Finite ((machine p main).Γ k) := inferInstanceAs (Finite Bool)

end IndependentSetsCut.CounterMachine

end OAI
