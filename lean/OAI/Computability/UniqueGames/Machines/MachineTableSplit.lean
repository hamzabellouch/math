import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.PCP.GraphTables
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

abbrev Tape := Fin 5
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .startVertices,
  .readVertices, .startDarts, .readDarts]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Tape 0 is protected input, 1 is the working row stream, 2 is scratch,
and 3 and 4 hold the extracted vertex and dart counts. -/
def tapes (original work vertices darts : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then original else if k = 1 then work
    else if k = 3 then vertices else if k = 4 then darts else []

def initialTapes (input : List Bool) : Tape → List Bool := tapes input [] [] []

def resultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  tapes (encodeWords [n, m] ++ rowsBits) rowsBits (encodeWord n) (encodeWord m)

@[simp] theorem resultTapes_original (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 0 = encodeWords [n, m] ++ rowsBits := by
  simp [resultTapes, tapes]

@[simp] theorem resultTapes_work (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 1 = rowsBits := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_scratch (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 2 = [] := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_vertices (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 3 = encodeWord n := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_darts (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 4 = encodeWord m := by simp [resultTapes, tapes]

/-- Six finite control labels, independent of all input sizes and contents. -/
def program {σ : Type} : Label → TM2.Stmt (fun _ : Tape => Bool) Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt 0 2 id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop 2 0 1 false .copySecond (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart 3 .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop 1 3 .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart 4 .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop 1 4 .readDarts none

def exactSteps (n m : Nat) (rowsBits : List Bool) : Nat :=
  2 * (encodeWords [n, m] ++ rowsBits).length + n + m + 6

theorem splitTrace {σ : Type} (n m : Nat) (rowsBits : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps n m rowsBits]
      (some ⟨some .copyFirst, (ambient, register),
        initialTapes (encodeWords [n, m] ++ rowsBits)⟩) =
      some ⟨none, (ambient, none), resultTapes n m rowsBits⟩ := by
  let word := encodeWords [n, m] ++ rowsBits
  let b₀ := initialTapes word
  let b₁ := tapes word word [] []
  let b₂ := tapes word (encodeWord m ++ rowsBits) (encodeWord n) []
  let b₃ := resultTapes n m rowsBits
  have h₀ : Function.update b₀ (1 : Tape) (b₀ 0 ++ b₀ 1) = b₁ := by
    funext k; fin_cases k <;> simp [b₀, b₁, initialTapes, tapes]
  have h₁ : Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ 3) = b₂ := by
    funext k; fin_cases k <;> simp [b₁, b₂, tapes, Hastad.SourceMachine.fieldTapes]
  have h₂ : Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂
      rowsBits (encodeWord m ++ b₂ 4) = b₃ := by
    funext k; fin_cases k <;>
      simp [b₂, b₃, resultTapes, tapes, word, Hastad.SourceMachine.fieldTapes]
  have copy := MachineCopy.copyTrace (0 : Tape) 1 2
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program (σ := σ)) rfl rfl b₀ (by simp [b₀, initialTapes, tapes]) ambient register
  rw [h₀] at copy
  have c₀ : (advance (TM2.step (program (σ := σ))))^[2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startVertices, (ambient, none), b₁⟩ := by
    simpa only [show b₀ 0 = word by simp [b₀, initialTapes, tapes]] using copy
  have scan₁ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 3 (by decide)
    .startVertices .readVertices (some .startDarts) (program (σ := σ)) rfl rfl
    b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, tapes, word, encodeWords, List.append_assoc]) ambient none).evals_in_steps
  have c₁ : (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₁
    change (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
      some ⟨some .startDarts, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁ (encodeWord m ++ rowsBits)
          (encodeWord n ++ b₁ 3)⟩ at scan₁
    simpa only [h₁] using scan₁
  have scan₂ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 4 (by decide)
    .startDarts .readDarts none (program (σ := σ)) rfl rfl
    b₂ m rowsBits (by simp [b₂, tapes]) ambient none).evals_in_steps
  have c₂ : (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₂
    change (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
      some ⟨none, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂ rowsBits
          (encodeWord m ++ b₂ 4)⟩ at scan₂
    simpa only [h₂] using scan₂
  have c₀₁ : (advance (TM2.step (program (σ := σ))))^[(n + 2) + 2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    rw [Function.iterate_add_apply, c₀, c₁]
  have c₀₁₂ : (advance (TM2.step (program (σ := σ))))^[(m + 2) +
      ((n + 2) + 2 * (word.length + 1))]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    rw [Function.iterate_add_apply, c₀₁, c₂]
  have count : exactSteps n m rowsBits = (m + 2) + ((n + 2) + 2 * (word.length + 1)) := by
    dsimp [exactSteps, word]
    omega
  rw [count]
  exact c₀₁₂

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 6

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 4 * length + 6 := by simp [timePolynomial]

theorem exactSteps_le (n m : Nat) (rowsBits : List Bool) :
    exactSteps n m rowsBits ≤ timePolynomial.eval (encodeWords [n, m] ++ rowsBits).length := by
  rw [timePolynomial_eval]
  simp only [exactSteps, List.length_append, encodeWords_length, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  omega

def splitInTime {σ : Type} (n m : Nat) (rowsBits : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ)))
      ⟨some .copyFirst, (ambient, register), initialTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨none, (ambient, none), resultTapes n m rowsBits⟩)
      (timePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) where
  steps := exactSteps n m rowsBits
  evals_in_steps := splitTrace n m rowsBits ambient register
  steps_le_m := exactSteps_le n m rowsBits

def machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .copyFirst
  σ := State Unit
  initialState := ((), none)
  m := program

theorem initial_configuration (input : List Bool) :
    initList machine input = ⟨some .copyFirst, ((), none), initialTapes input⟩ := by
  have ht : (initList machine input).stk = initialTapes input := by
    let : Fintype machine.K := (inferInstance : Fintype Tape)
    funext k; fin_cases k <;> simp [initList, machine, initialTapes, tapes]; rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

def rowsBits (table : PCP.GraphTables.Table) : List Bool :=
  encodeWords ((PCP.GraphTables.rowList table).flatMap PCP.GraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GraphTables.Table) :
    PCP.GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table := by
  simp only [PCP.GraphTables.tableBits, PCP.GraphTables.tableWords, encodeWords_append, rowsBits]

theorem tableTrace {σ : Type} (table : PCP.GraphTables.Table) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps table.vertices table.darts (rowsBits table)]
      (some ⟨some .copyFirst, (ambient, register), initialTapes (PCP.GraphTables.tableBits table)⟩) =
      some ⟨none, (ambient, none), resultTapes table.vertices table.darts (rowsBits table)⟩ := by
  rw [tableBits_header_rows]
  exact splitTrace table.vertices table.darts (rowsBits table) ambient register

/-- The concrete machine starts at its genuine initial configuration on a full
graph table and leaves every output field on the stated physical tape. -/
def initializedTableInTime (table : PCP.GraphTables.Table) :
    StateTransition.EvalsToInTime machine.step (initList machine (PCP.GraphTables.tableBits table))
      (some ⟨none, ((), none), resultTapes table.vertices table.darts (rowsBits table)⟩)
      (timePolynomial.eval (PCP.GraphTables.tableBits table).length) := by
  rw [initial_configuration, tableBits_header_rows]
  exact splitInTime table.vertices table.darts (rowsBits table) () none

end UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

end OAI
