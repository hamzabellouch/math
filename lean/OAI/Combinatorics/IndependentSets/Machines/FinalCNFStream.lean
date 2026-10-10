import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.FinalCNFHeader
import OAI.Combinatorics.IndependentSets.Machines.FinalCNFRow

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

def remainingEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).drop r

def processedEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).take r

def inputStream (table : GraphTables.Table) (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => encodeWords (GraphTables.rowWords table.rows[e]))

def outputStream (plan : Plan) (table : GraphTables.Table)
    (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => plan.flatMap (Emitter.commandBits (rowOperands table e)
    (rowRelation table e)))

@[simp] theorem remainingEvents_zero (table : GraphTables.Table) :
    remainingEvents table 0 = List.finRange table.darts := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_length (table : GraphTables.Table) (r : Nat) :
    (remainingEvents table r).length = table.darts - r := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_done (table : GraphTables.Table) :
    remainingEvents table table.darts = [] := by
  simp [remainingEvents]

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

@[simp] theorem processedEvents_zero (table : GraphTables.Table) :
    processedEvents table 0 = [] := by simp [processedEvents]

@[simp] theorem processedEvents_done (table : GraphTables.Table) :
    processedEvents table table.darts = List.finRange table.darts := by
  simp [processedEvents]

theorem processedEvents_succ (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    processedEvents table (r + 1) = processedEvents table r ++ [⟨r, h⟩] := by
  unfold processedEvents
  rw [List.take_succ_eq_append_getElem (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

theorem processed_append_remaining (table : GraphTables.Table) (r : Nat) :
    processedEvents table r ++ remainingEvents table r = List.finRange table.darts := by
  exact List.take_append_drop r (List.finRange table.darts)

@[simp] theorem inputStream_nil (table : GraphTables.Table) : inputStream table [] = [] := rfl

@[simp] theorem inputStream_cons (table : GraphTables.Table) (e : Fin table.darts)
    (events : List (Fin table.darts)) :
    inputStream table (e :: events) =
      encodeWords (GraphTables.rowWords table.rows[e]) ++ inputStream table events := rfl

@[simp] theorem inputStream_append (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    inputStream table (first ++ rest) = inputStream table first ++ inputStream table rest := by
  simp only [inputStream, List.flatMap_append]

@[simp] theorem outputStream_nil (plan : Plan) (table : GraphTables.Table) :
    outputStream plan table [] = [] := rfl

@[simp] theorem outputStream_cons (plan : Plan) (table : GraphTables.Table)
    (e : Fin table.darts) (events : List (Fin table.darts)) :
    outputStream plan table (e :: events) =
      plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e)) ++
        outputStream plan table events := rfl

@[simp] theorem outputStream_append (plan : Plan) (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    outputStream plan table (first ++ rest) =
      outputStream plan table first ++ outputStream plan table rest := by
  simp only [outputStream, List.flatMap_append]

theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]

theorem outputStream_processed_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (processedEvents table (r + 1)) =
      outputStream plan table (processedEvents table r) ++
        plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
          (rowRelation table ⟨r, h⟩)) := by
  rw [processedEvents_succ table r h, outputStream_append]
  simp

theorem inputStream_split (table : GraphTables.Table) (r : Nat) :
    inputStream table (List.finRange table.darts) =
      inputStream table (processedEvents table r) ++
        inputStream table (remainingEvents table r) := by
  rw [← inputStream_append, processed_append_remaining]

theorem outputStream_split (plan : Plan) (table : GraphTables.Table) (r : Nat) :
    outputStream plan table (List.finRange table.darts) =
      outputStream plan table (processedEvents table r) ++
        outputStream plan table (remainingEvents table r) := by
  rw [← outputStream_append, processed_append_remaining]

private theorem encodeWords_flatMap_rows {α : Type} (rows : List α) (words : α → List Nat) :
    encodeWords (rows.flatMap words) = rows.flatMap (fun row => encodeWords (words row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits (genericTable table) := by
  rw [tableRowsBits, genericTable_rowList]
  erw [List.flatMap_map]
  change inputStream table (List.finRange table.darts) =
    encodeWords ((GraphTables.rowList table).flatMap
      (fun row => GenericGraphTables.rowWords (genericRow row)))
  simp only [genericRow_words]
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap_rows]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits (genericTable table) := by
  rw [remainingEvents_zero, inputStream_all]

theorem outputStream_accumulator_succ (plan : Plan) (table : GraphTables.Table)
    (r : Nat) (h : r < table.darts) (header : List Bool) :
    (plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
      (rowRelation table ⟨r, h⟩))).reverse ++
        (header ++ outputStream plan table (processedEvents table r)).reverse =
      (header ++ outputStream plan table (processedEvents table (r + 1))).reverse := by
  rw [outputStream_processed_succ plan table r h]
  simp only [List.reverse_append, List.append_assoc]

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
