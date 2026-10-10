import Mathlib
import OAI.Computability.MaxCut.PCP.ExpanderFamily

namespace OAI

namespace MaxCutGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d
abbrev rowFactor (d : Nat) : Nat := cloudSize d * degree d

/-- The encoded vertex of `firstH` already stores both square ports.
The two graph-return registers and final-H register are overwritten by the
corresponding callbacks. Every field is bounded independently of table size. -/
structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

/-- Consume the finite cloud coordinate and input port, and perform the first
lookup in the fixed table. Initial register values need no inhabitance choice. -/
def start {d : Nat} (H : Table (cloudSize d) d)
    (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : Control d :=
  let ports := (rowIndex d d).symm port
  let first := lookup H (cloud, ports.1)
  let square := (rowIndex (degree d) (degree d)).symm first.1
  { firstH := first
    lastInput := ports.2
    firstG := square.1
    secondG := square.2
    lastH := first }

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

/-- The second graph remainder completes the final lookup in the fixed table.
The square return ports are ordered second, first, as in `stepLookup`. -/
def receiveSecond {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with
    secondG := returnedPort
    lastH := lookup H
      (rowIndex (degree d) (degree d) (returnedPort,s.firstG),s.lastInput) }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

/-- The entire bounded contribution to the emitted row: output port plus
`q` times output cloud, with `q = d*d`. -/
def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def firstAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (firstOffset s).val

def secondAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (secondOffset s).val

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

@[simp] theorem receiveSecond_port {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (r : Fin (degree d)) : (receiveSecond H s r).secondG = r := rfl

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem secondAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s =
      (rowIndex v (degree d) (vertex,secondOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem firstAddress_lt {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s < v * degree d := by
  rw [firstAddress_eq_rowIndex]
  exact (rowIndex v (degree d) (vertex,firstOffset s)).isLt

theorem secondAddress_lt {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s < v * degree d := by
  rw [secondAddress_eq_rowIndex]
  exact (rowIndex v (degree d) (vertex,secondOffset s)).isLt

/-- Actual table returns split into the unary vertex quotient and finite port
remainder. Both formulas are the definitions of the table's mixed-radix inverse. -/
theorem lookup_vertex_div {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    (lookup G x).1.val = (reverseIndex G (rowIndex v q x)).val / q := rfl

theorem lookup_port_mod {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    (lookup G x).2.val = (reverseIndex G (rowIndex v q x)).val % q := rfl

theorem lookup_port_eq_remainder {v q : Nat} (G : Table v q) (x : Fin v × Fin q)
    (r : Fin q) (hr : r.val = (reverseIndex G (rowIndex v q x)).val % q) :
    (lookup G x).2 = r := Fin.ext ((lookup_port_mod G x).trans hr.symm)

theorem rowIndex_lookup {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    rowIndex v q (lookup G x) = reverseIndex G (rowIndex v q x) := by
  simp only [lookup, Equiv.apply_symm_apply]

def outputPair {v d : Nat} (vertex : Fin v) (s : Control d) :
    Fin (v * cloudSize d) × Fin (degree d) :=
  (rowIndex v (cloudSize d) (vertex,s.lastH.1),outputPort s)

theorem outputAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    outputAddress vertex.val s =
      (rowIndex (v * cloudSize d) (degree d) (outputPair vertex s)).val := by
  simp only [outputAddress, outputOffset, outputPair, rowIndex_val, rowFactor]
  ring

theorem outputAddress_lt {v d : Nat} (vertex : Fin v) (s : Control d) :
    outputAddress vertex.val s < (v * cloudSize d) * degree d := by
  rw [outputAddress_eq_rowIndex]
  exact (rowIndex (v * cloudSize d) (degree d) (outputPair vertex s)).isLt

/-- Pure row semantics: exactly two lookups in the input table. The two fixed
H lookups occur inside `start` and `receiveSecond`. This is not a machine trace. -/
def evaluateRow {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    Fin v × Control d :=
  let s₀ := start H cloud port
  let g₁ := lookup G (vertex,firstOffset s₀)
  let s₁ := receiveFirst s₀ g₁.2
  let g₂ := lookup G (g₁.1,secondOffset s₁)
  (g₂.1, receiveSecond H s₁ g₂.2)

/-- The finite callback sequence computes exactly the previously checked
square/zigzag lookup, including both reversed square ports. -/
theorem evaluateRow_eq_lookup_step {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputPair (evaluateRow G H vertex cloud port).1 (evaluateRow G H vertex cloud port).2 =
      lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port) := by
  rw [lookup_step]
  simp only [evaluateRow, start, receiveFirst, receiveSecond, firstOffset, secondOffset,
    squarePorts, outputPair, outputPort, stepLookup, Equiv.symm_apply_apply]

theorem outputAddress_eq_step_row {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (rowIndex (v * cloudSize d) (degree d)
        (lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_rowIndex, evaluateRow_eq_lookup_step]

/-- The emitted natural number is the actual stored row, not just an
extensionally equivalent endpoint pair. -/
theorem outputAddress_eq_step_reverseIndex {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (reverseIndex (step G H) (rowIndex (v * cloudSize d) (degree d)
        (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_step_row, rowIndex_lookup]

end MaxCutGames.Foundations.PCP.ExpanderRowControl

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open MaxCutGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

theorem rotationWords_getElem (table : Table v d) (i : ℕ) (hi : i < v * d) :
    (rotationWords table)[i]'(by simpa only [rotationWords_length] using hi) =
      (reverseIndex table ⟨i, hi⟩).val := by
  simp only [rotationWords, List.getElem_map, Vector.getElem_toList,
    reverseIndex, Fin.getElem_fin]

theorem rotationWords_get (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table).get
      ⟨i.val, by simpa only [rotationWords_length] using i.isLt⟩ =
      (reverseIndex table i).val := by
  simpa only [List.get_eq_getElem] using rotationWords_getElem table i.val i.isLt

/-- The exact zero-based lookup hypothesis consumed by the machine lookup API. -/
theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

theorem rotationWords_getElem?_none (table : Table v d) (i : ℕ) (hi : v * d ≤ i) :
    (rotationWords table)[i]? = none :=
  List.getElem?_eq_none (by simpa only [rotationWords_length] using hi)

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

/-- The serialized reverse index decodes to the actual table lookup. -/
theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

/-- Both the input and output use port-first mixed-radix row coordinates. -/
theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

@[simp] theorem decode_rotationWords (table : Table v d) :
    decodeWords (encodeWords (rotationWords table)) = some (rotationWords table) :=
  Complexity.decodeWords_encodeWords _

/-- Fully decode the serialized list, then select the actual reverse-dart row. -/
theorem decoded_lookup (table : Table v d) (i : Fin (v * d)) :
    (decodeWords (encodeWords (rotationWords table))).bind (fun words => words[i.val]?) =
      some (reverseIndex table i).val := by
  rw [decode_rotationWords]
  exact rotationWords_getElem? table i

theorem decoded_coordinate_lookup (table : Table v d) (x : Fin v × Fin d) :
    (decodeWords (encodeWords (rotationWords table))).bind
        (fun words => words[x.2.val + d * x.1.val]?) =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  rw [decode_rotationWords]
  exact rotationWords_row_order table x

theorem encode_rotationWords_length_eq (table : Table v d) :
    (encodeWords (rotationWords table)).length = (rotationWords table).sum + v * d := by
  rw [Complexity.encodeWords_length, rotationWords_length]

/-- Complete raw-row serialization bound, with no discarded delimiter or prefix. -/
theorem encode_rotationWords_length_le (table : Table v d) :
    (encodeWords (rotationWords table)).length ≤ (v * d) * (v * d + 1) := by
  calc
    _ ≤ (rotationWords table).length * (v * d + 1) :=
      Complexity.encodeWords_length_le _ _
        (fun n hn => (rotationWords_entry_lt table n hn).le)
    _ = _ := by rw [rotationWords_length]

end MaxCutGames.Foundations.PCP.ExpanderTableWords

end OAI
