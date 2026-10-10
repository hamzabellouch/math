import OAI.Computability.UniqueGames.Games.ProductLemmas
import OAI.Computability.UniqueGames.Machines.MachineProductFieldLemmas

namespace OAI

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

namespace UniqueGamesTheorem.Explicit.ProductMachineSemantics

open UniqueGamesTheorem.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

/-- Indexing a flattened constant-width row list preserves the literal field
position, not merely the multiset of row contents. -/
theorem row_table_lookup (constraints : List (Constraint n q))
    (e : Fin constraints.length) (field : Fin (q + 2)) :
    (constraints.flatMap constraintWords)[(q + 2) * e.val + field.val]? =
      (constraintWords constraints[e])[field.val]? := by
  induction constraints with
  | nil => exact Fin.elim0 e
  | cons c constraints ih =>
    refine Fin.cases ?_ (fun i => ?_) e
    · simp [List.flatMap_cons, List.getElem?_append, constraintWords_length, field.isLt]
    · rw [List.flatMap_cons, List.getElem?_append]
      have hlarge : ¬ (q + 2) * i.succ.val + field.val < (constraintWords c).length := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [ite_eq_right hlarge]
      have hindex : (q + 2) * i.succ.val + field.val - (constraintWords c).length =
          (q + 2) * i.val + field.val := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [hindex]
      exact ih i

def inputTable (H : Instance q) : List ℕ := H.constraints.flatMap constraintWords

theorem inputTable_source (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val]? = some H.constraints[e].source.val := by
  have h := row_table_lookup H.constraints e (⟨0, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_target (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val + 1]? = some H.constraints[e].target.val := by
  have h := row_table_lookup H.constraints e (⟨1, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_image (H : Instance q) (e : Fin H.constraints.length) (a : Fin q) :
    (inputTable H)[(q + 2) * e.val + (2 + a.val)]? =
      some (H.constraints[e].permutation.images[a]).val := by
  have h := row_table_lookup H.constraints e (⟨2 + a.val, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords, tableWords, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

def reverseDigits (fields : Fin t → ℕ) (i : ℕ) : ℕ :=
  if h : i < t then fields (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_at (fields : Fin t → ℕ) (i : Fin t) :
    reverseDigits fields i.val = fields i.rev := by simp [reverseDigits, i.isLt]

theorem reverseDigits_words (fields : Fin t → ℕ) :
    (List.range t).map (reverseDigits fields) = (List.ofFn fields).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < t := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, reverseDigits, hi', ↓reduceDIte,
      List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Fin.rev]
    apply congrArg fields
    apply Fin.ext
    change t - (i + 1) = t - 1 - i
    omega

theorem horner_ofFin {radix : ℕ} (fields : Fin t → Fin radix) :
    MachineHorner.value radix (reverseDigits (fun i => (fields i : ℕ))) t =
      (finFunctionFinEquiv fields : ℕ) := by
  rw [MachineHorner.value_eq_foldl, reverseDigits_words,
    ← ProductTarget.address_eq_horner]

def sourceCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 0)
def targetCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 1)
def imageCommand (q t : ℕ) (a : Fin (q ^ t)) : MachineProductRow.Command t :=
  (true, fun i => 2 + (finFunctionFinEquiv.symm a i).val)

/-- The complete fixed-alphabet row schedule: two endpoints followed by every
forward-table entry in increasing numeric label order. -/
def commands (q t : ℕ) : List (MachineProductRow.Command t) :=
  sourceCommand t :: targetCommand t :: (List.finRange (q ^ t)).map (imageCommand q t)

theorem commands_length (q t : ℕ) : (commands q t).length = q ^ t + 2 := by
  simp [commands]

def fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : Fin t → ℕ := fun j =>
  ((inputTable H)[(q + 2) * (edges j).val + command.2 j]?).getD 0

def fieldValue (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : ℕ :=
  MachineHorner.value (if command.1 then q else H.vertices)
    (reverseDigits (fields H edges command)) t

theorem source_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (sourceCommand t) = fun j => H.constraints[edges j].source.val := by
  funext j
  simp [fields, sourceCommand, inputTable_source]

theorem target_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (targetCommand t) = fun j => H.constraints[edges j].target.val := by
  funext j
  simp [fields, targetCommand, inputTable_target]

theorem image_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fields H edges (imageCommand q t a) = fun j =>
      (H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]).val := by
  funext j
  unfold fields imageCommand
  rw [inputTable_image H (edges j) (finFunctionFinEquiv.symm a j)]
  rfl

/-- Every scheduled lookup selects an actual word in the input table. -/
theorem selected (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    (inputTable H)[(q + 2) * (edges i).val + c.2 i]? =
      some (fields H edges c i) := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, sourceCommand, inputTable_source]
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, targetCommand, inputTable_target]
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact inputTable_image H (edges i) (finFunctionFinEquiv.symm a i)

theorem command_offset_lt (c : MachineProductRow.Command t)
    (hc : c ∈ commands q t) (i : Fin t) : c.2 i < q + 2 := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [sourceCommand]
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [targetCommand]
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  have h := (finFunctionFinEquiv.symm a i).isLt
  simp only [imageCommand]
  omega

theorem fields_lt (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    fields H edges c i < if c.1 then q else H.vertices := by
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [source_fields]
    exact H.constraints[edges i].source.isLt
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [target_fields]
    exact H.constraints[edges i].target.isLt
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact (H.constraints[edges i].permutation.images[finFunctionFinEquiv.symm a i]).isLt

theorem source_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (sourceCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].source) : ℕ) := by
  unfold fieldValue
  rw [source_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].source)

theorem target_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (targetCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].target) : ℕ) := by
  unfold fieldValue
  rw [target_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].target)

theorem image_value (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fieldValue H edges (imageCommand q t a) =
      (finFunctionFinEquiv (fun j =>
        H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]) : ℕ) := by
  unfold fieldValue
  rw [image_fields]
  exact horner_ofFin (fun j =>
    H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j])

private theorem encodeWords_map {X : Type*} (xs : List X) (f : X → ℕ) :
    encodeWords (xs.map f) = xs.flatMap (fun x => encodeWord (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih]

/-- The controller's literal field-command output is the serialized semantic
row, including every forward permutation-table entry. -/
theorem rowBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t) =
      encodeWords (constraintWords (ProductPaddedOutput.outputRow H presentation t ht i)) := by
  have hsource : fieldValue H (finFunctionFinEquiv.symm i) (sourceCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).source.val := source_value _ _
  have htarget : fieldValue H (finFunctionFinEquiv.symm i) (targetCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).target.val := target_value _ _
  have himage (a : Fin (q ^ t)) :
      fieldValue H (finFunctionFinEquiv.symm i) (imageCommand q t a) =
      ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val := by
    rw [ProductPaddedOutput.outputRow_images]
    exact image_value _ _ _
  simp only [MachineProductRow.rowBits, commands, List.flatMap_cons, List.flatMap_map,
    hsource, htarget, himage, constraintWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]
  congr 2
  have htable : tableWords (ProductPaddedOutput.outputRow H presentation t ht i).permutation =
      (List.finRange (q ^ t)).map
        (fun a => ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val) := by
    apply List.ext_getElem
    · simp [tableWords]
    · intro j hj hk
      simp [tableWords, Fin.getElem_fin]
  rw [htable, encodeWords_map]

private theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List ℕ) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords_append, ih]

/-- Product rows are emitted in ascending radix address, exactly the literal
order of the output constraint list. -/
def allRowsBits (H : Instance q) (t : ℕ) : List Bool :=
  (List.finRange (H.constraints.length ^ t)).flatMap (fun i =>
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t))

theorem allRowsBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    allRowsBits H t = encodeWords
      ((ProductPaddedOutput.output H presentation t ht).constraints.flatMap constraintWords) := by
  unfold allRowsBits
  simp_rw [rowBits_eq H presentation t ht]
  rw [ProductPaddedOutput.output_constraints]
  have hrows : List.ofFn (ProductPaddedOutput.outputRow H presentation t ht) =
      (List.finRange (H.constraints.length ^ t)).map
        (ProductPaddedOutput.outputRow H presentation t ht) := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  rw [hrows]
  erw [List.flatMap_map, encodeWords_flatMap]
  rfl

/-- Concatenating the three computed headers and all physical row fields yields
precisely the target serialization, including list order and full tables. -/
theorem gameBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++ allRowsBits H t =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  rw [gameBits, ProductPaddedOutput.output_gameWords, encodeWords_append,
    allRowsBits_eq H presentation t ht, ProductPaddedOutput.output_constraints]
  rfl

end UniqueGamesTheorem.Explicit.ProductMachineSemantics

end OAI
