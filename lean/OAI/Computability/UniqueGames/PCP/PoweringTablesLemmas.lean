import OAI.Computability.UniqueGames.Machines.PoweringMachineRow
import OAI.Computability.UniqueGames.PCP.CloudRoundingLemmas
import OAI.Computability.UniqueGames.PCP.GenericGraphTables
import OAI.Computability.UniqueGames.PCP.PoweringLabelsLemmas
import OAI.Computability.UniqueGames.PCP.PoweringOpinionTables

namespace OAI

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

/-- Program-constant output alphabet size for degree `d` and walk length `n+1`. -/
def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

/-- Number of directed recorded-walk occurrences, including orientation. -/
def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

def mathematicalGraph {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    ConstraintGraph (Fin vertices) (PoweringTest.Dart (Fin vertices) (Fin d) n)
      (PaddedLabel (Fin d) (n + 1) (Fin 64)) :=
  PoweringTest.poweredGraph (PortTables.portGraph input) (PortTables.accepts input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1))

/-- The finite first-address predicate evaluator used for each stored row. -/
def rowAccepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) : Bool :=
  let rows := PoweringOpinionTables.walkRows (PortTables.portGraph input) n e.2
  let left := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 a)
  let right := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 b)
  if e.1 then PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows right left
    else PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows left right

theorem rowAccepts_eq {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) :
    rowAccepts input n e a b = (mathematicalGraph input n).accepts e
      (decodeLabel d (n + 1) 64 a) (decodeLabel d (n + 1) 64 b) := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowAccepts, mathematicalGraph, PoweringTest.poweredGraph, Bool.false_eq_true,
      ite_false, ite_true, PoweringOpinionTables.rowsAccepts_walkRows]

def table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.Table (labelCount d n) :=
  GenericGraphTables.ofEnumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
    (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64)

@[simp] theorem table_vertices {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).vertices = vertices := rfl

@[simp] theorem table_darts {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).darts = dartCount vertices d n := rfl

/-- Complete decoded semantics, with executable vertex, dart and label orders. -/
theorem semantics_table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.semantics (table input n) =
      GenericGraphTables.enumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
        (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) :=
  GenericGraphTables.semantics_ofGraph _

/-- Each actual output relation entry is the bounded stored-opinion evaluator. -/
theorem table_accepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (dartCount vertices d n)) (a b : Fin (labelCount d n)) :
    GenericGraphTables.acceptsAt (table input n).rows i a b =
      rowAccepts input n (decodeDart vertices d n i) a b := by
  change (GenericGraphTables.semantics (table input n)).accepts i a b = _
  rw [semantics_table]
  exact (rowAccepts_eq input n (decodeDart vertices d n i) a b).symm

/-- The reverse row flips just the orientation in the recorded-walk encoding. -/
theorem table_reverse {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (direction : Bool) (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    GenericGraphTables.reverseAt (table input n).rows (encodeDart vertices d n (direction, w)) =
      encodeDart vertices d n (!direction, w) := by
  change (GenericGraphTables.semantics (table input n)).reverse _ = _
  rw [semantics_table]
  change dartEquiv vertices d n ((mathematicalGraph input n).reverse
      ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, w)))) =
    dartEquiv vertices d n (!direction, w)
  rw [(dartEquiv vertices d n).symm_apply_apply]
  rfl

/-- Serialized output in the shared generic graph codec. -/
def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

/-- The actual function on variable-size regular input tables. -/
def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end UniqueGamesTheorem.Foundations.PCP.PoweringTables

/-!
# Actual graph data consumed by the powered-row machine

The data fields are computed from the stored rotor and base relations. The
endpoint masks compare actual bounded word endpoints, in `allAddresses` order.
Their first true positions equal the already checked canonical address indices.

Reversing a row swaps the two masks and transposes each base predicate. Thus
one fixed row machine handles both directions. Its label lookup depends only
on the fixed degree and radius. The final identities describe the exact unary
input fields and the exact serialized relation emitted for a stored output row.

These are semantic producer-to-emitter identities. A machine implementation
that computes the input data from the serialized rotor is a separate frontend.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowData

open UniqueGamesTheorem.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

/-- The row machine scans the same increasing address-index order. -/
theorem firstMatch_of_first {S : Nat} (mask : Fin S → Bool) (i : Fin S)
    (hi : mask i = true) (hfirst : ∀ j : Fin S, j.val < i.val → mask j = false) :
    firstMatch mask = some i := by
  unfold firstMatch
  apply List.find?_ofFn_eq_some.mpr
  refine ⟨hi, i, rfl, ?_⟩
  intro j hj
  change ¬mask j = true
  simp [hfirst j hj]

theorem firstMatch_firstIndex {X : Type*} (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) :
    firstMatch (fun i : Fin xs.length => decide (p (xs.get i))) =
      some (firstIndex p xs h) := by
  apply firstMatch_of_first
  · exact decide_eq_true (firstIndex_matches p xs h)
  · intro j hj
    exact decide_eq_false (firstIndex_is_first p xs h j hj)

/-- An actual endpoint comparison; it has no reachability oracle input. -/
def endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center target : Fin vertices) (i : AddressIndex d t) : Bool :=
  decide ((wordToBall G t center ((allAddresses d t).get i)).val = target)

theorem firstMatch_endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    firstMatch (endpointMask G t center u.val) = some (addressIndex G t center u) := by
  unfold endpointMask addressIndex
  exact firstMatch_firstIndex
    (fun w : PortWords (Fin d) t => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

def slotCount (d n : Nat) : Nat := (allAddresses d (n + 1)).length

abbrev RowBuffer (d n : Nat) := Buffer (inputSize (n + 1) (slotCount d n))

/-- This lookup is fixed by the reduction parameters, not the input graph. -/
def fixedLabelAt (d n : Nat) (a : Fin (PoweringTables.labelCount d n))
    (i : Fin (slotCount d n)) : GraphTables.Label :=
  decodeLabel d (n + 1) 64 a ((allAddresses d (n + 1)).get i)

theorem fixedLabelAt_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (center : Fin vertices) (u : Ball G (n + 1) center)
    (a : Fin (PoweringTables.labelCount d n)) :
    fixedLabelAt d n a (addressIndex G (n + 1) center u) =
      decode (finitePortSelector G (n + 1) center) (decodeLabel d (n + 1) 64 a) u := by
  simpa only [fixedLabelAt, labelTable_get] using
    labelTable_addressIndex G (n + 1) center u (decodeLabel d (n + 1) 64 a)

/-- For each actual path edge, store its complete base relation, then the
start-to-tail mask, then the end-to-head mask. Every bit is computed. -/
def walkData (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (k : Fin (n + 1)) : Field (slotCount d n) → Bool
  | .inl (a, b) => PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k) a b
  | .inr (.inl i) => endpointMask (PortTables.portGraph input) (n + 1) w.1
      (edgeAt (PortTables.portGraph input) n w k).1 i
  | .inr (.inr i) => endpointMask (PortTables.portGraph input) (n + 1)
      (endpoint (PortTables.portGraph input) w)
      ((PortTables.portGraph input).rot (edgeAt (PortTables.portGraph input) n w k)).1 i

def walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : RowBuffer d n :=
  packData (walkData input n w)

@[simp] theorem basePredicate_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a b : GraphTables.Label) :
    basePredicate (walkBits input n w) k a b =
      PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k) a b := by
  simp [basePredicate, walkBits, walkData]

@[simp] theorem leftMatches_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    leftMatches (walkBits input n w) k = endpointMask (PortTables.portGraph input)
      (n + 1) w.1 (edgeAt (PortTables.portGraph input) n w k).1 := by
  funext i
  simp [leftMatches, walkBits, walkData]

@[simp] theorem rightMatches_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    rightMatches (walkBits input n w) k = endpointMask (PortTables.portGraph input)
      (n + 1) (endpoint (PortTables.portGraph input) w)
      ((PortTables.portGraph input).rot (edgeAt (PortTables.portGraph input) n w k)).1 := by
  funext i
  simp [rightMatches, walkBits, walkData]

theorem firstMatch_walkBits_left (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    firstMatch (leftMatches (walkBits input n w) k) = some
      (addressIndex (PortTables.portGraph input) (n + 1) w.1
        (tailFromStart (PortTables.portGraph input) n w k)) := by
  rw [leftMatches_walkBits]
  simpa only [tailFromStart_val, slotCount] using
    firstMatch_endpointMask (PortTables.portGraph input) (n + 1) w.1
      (tailFromStart (PortTables.portGraph input) n w k)

theorem firstMatch_walkBits_right (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    firstMatch (rightMatches (walkBits input n w) k) = some
      (addressIndex (PortTables.portGraph input) (n + 1)
        (endpoint (PortTables.portGraph input) w)
        (headFromEnd (PortTables.portGraph input) n w k)) := by
  rw [rightMatches_walkBits]
  simpa only [headFromEnd_val, slotCount] using
    firstMatch_endpointMask (PortTables.portGraph input) (n + 1)
      (endpoint (PortTables.portGraph input) w) (headFromEnd (PortTables.portGraph input) n w k)

theorem edgeAccept_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a b : Fin (PoweringTables.labelCount d n)) :
    edgeAccept (fixedLabelAt d n) (walkBits input n w) k a b =
      PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k)
        (decode (finitePortSelector (PortTables.portGraph input) (n + 1) w.1)
          (decodeLabel d (n + 1) 64 a) (tailFromStart (PortTables.portGraph input) n w k))
        (decode (finitePortSelector (PortTables.portGraph input) (n + 1)
          (endpoint (PortTables.portGraph input) w))
          (decodeLabel d (n + 1) 64 b) (headFromEnd (PortTables.portGraph input) n w k)) := by
  simp only [edgeAccept, firstMatch_walkBits_left, firstMatch_walkBits_right,
    basePredicate_walkBits, fixedLabelAt_addressIndex]

theorem rowAccept_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowAccept (fixedLabelAt d n) (walkBits input n w) a b =
      rowsAccepts (PortTables.accepts input) (walkRows (PortTables.portGraph input) n w)
        (labelTable (decodeLabel d (n + 1) 64 a))
        (labelTable (decodeLabel d (n + 1) 64 b)) := by
  rw [rowsAccepts_walkRows]
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, PoweringTest.pathAccepts_eq_true_iff, edgeAccept_walkBits]

/-- Reverse orientation exchanges the two mask fields and label arguments. -/
def transposeField {S : Nat} : Field S → Field S
  | .inl (a, b) => .inl (b, a)
  | .inr (.inl i) => .inr (.inr i)
  | .inr (.inr i) => .inr (.inl i)

def transposeBits {t S : Nat} (bits : Buffer (inputSize t S)) : Buffer (inputSize t S) :=
  packData fun k field => bits (inputEquiv t S (k, transposeField field))

@[simp] theorem basePredicate_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : GraphTables.Label) :
    basePredicate (transposeBits bits) k a b = basePredicate bits k b a := by
  simp [basePredicate, transposeBits, transposeField]

@[simp] theorem leftMatches_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) :
    leftMatches (transposeBits bits) k = rightMatches bits k := by
  funext i
  simp [leftMatches, rightMatches, transposeBits, transposeField]

@[simp] theorem rightMatches_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) :
    rightMatches (transposeBits bits) k = leftMatches bits k := by
  funext i
  simp [leftMatches, rightMatches, transposeBits, transposeField]

theorem edgeAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) :
    edgeAccept labelAt (transposeBits bits) k a b = edgeAccept labelAt bits k b a := by
  simp only [edgeAccept, leftMatches_transposeBits, rightMatches_transposeBits]
  cases hl : firstMatch (leftMatches bits k) <;>
    cases hr : firstMatch (rightMatches bits k) <;>
    simp

theorem rowAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt (transposeBits bits) a b = rowAccept labelAt bits b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, edgeAccept_transposeBits]

/-- The fully specified data block for either directed occurrence. -/
def rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : RowBuffer d n :=
  if e.1 then transposeBits (walkBits input n e.2) else walkBits input n e.2

def rowData (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) : Bool :=
  walkData input n e.2 k (if e.1 then transposeField field else field)

theorem rowBits_packData (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    rowBits input n e = packData (rowData input n e) := by
  rcases e with ⟨direction, w⟩
  cases direction <;> funext i <;>
    simp [rowBits, rowData, transposeBits, walkBits, packData]

@[simp] theorem rowBits_field (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    rowBits input n e (inputEquiv (n + 1) (slotCount d n) (k, field)) =
      rowData input n e k field := by
  rw [rowBits_packData, packData_inputEquiv]

/-- No match-mask or base-relation premise remains in the evaluator bridge. -/
theorem rowAccept_rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowAccept (fixedLabelAt d n) (rowBits input n e) a b =
      PoweringTables.rowAccepts input n e a b := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowBits, Bool.false_eq_true, ite_false, ite_true,
      rowAccept_transposeBits, rowAccept_walkBits, PoweringTables.rowAccepts]

theorem rowBlock_at_rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowBlock (fixedLabelAt d n) (rowBits input n e)
        (GenericGraphTables.relationIndex (PoweringTables.labelCount d n) (a, b)) =
      PoweringTables.rowAccepts input n e a b := by
  rw [rowBlock_at, rowAccept_rowBits]

def dataWords (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Nat :=
  (List.ofFn (rowBits input n e)).map GraphTables.bitWord

def dataTape (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Bool :=
  encodeWords (dataWords input n e)

theorem dataTape_eq (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    dataTape input n e = encodeBits (List.ofFn (rowBits input n e)) :=
  (encodeBits_graphWords _).symm

theorem dataWords_length (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (dataWords input n e).length = (n + 1) * (4096 + (slotCount d n + slotCount d n)) := by
  rw [dataWords, List.length_map]
  simpa only [inputSize] using (List.length_ofFn (f := rowBits input n e))

theorem dataTape_length_le (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (dataTape input n e).length ≤ 2 * inputSize (n + 1) (slotCount d n) := by
  rw [dataTape_eq]
  simpa only [List.length_ofFn] using encodeBits_length_le (List.ofFn (rowBits input n e))

def emittedRelation (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    GenericGraphTables.RelationTable (PoweringTables.labelCount d n) :=
  Vector.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))

theorem emittedRelation_eq (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    emittedRelation input n e = GenericGraphTables.relationOf (PoweringTables.rowAccepts input n e) := by
  unfold emittedRelation GenericGraphTables.relationOf
  apply congrArg Vector.ofFn
  funext i
  exact rowAccept_rowBits input n e _ _

theorem rowBlock_unary (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    encodeBits (List.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))) =
      encodeWords (GenericGraphTables.relationWords (emittedRelation input n e)) := by
  have hbit : GraphTables.bitWord = GenericGraphTables.bitWord := by
    funext b
    cases b <;> rfl
  have h := encodeBits_graphWords
    (List.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e)))
  rw [hbit] at h
  simpa only [emittedRelation, GenericGraphTables.relationWords, Vector.toList_ofFn] using h

/-- The emitted bits are the relation of the actual numbered output row. -/
theorem emittedRelation_table (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (PoweringTables.dartCount vertices d n)) :
    emittedRelation input n (decodeDart vertices d n i) =
      (PoweringTables.table input n).rows[i].relation := by
  apply Vector.ext
  intro j hj
  have h := PoweringTables.table_accepts input n i
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).1
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).2
  have hindex : GenericGraphTables.relationIndex (PoweringTables.labelCount d n)
      (((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).1,
        ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).2) =
        ⟨j, hj⟩ := by
    change GenericGraphTables.relationIndex (PoweringTables.labelCount d n)
      ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩) = _
    exact Equiv.apply_symm_apply _ _
  simp only [GenericGraphTables.acceptsAt, GenericGraphTables.relationAt, hindex,
    Fin.getElem_fin] at h
  simp only [emittedRelation, Vector.getElem_ofFn]
  change rowBlock (fixedLabelAt d n) (rowBits input n (decodeDart vertices d n i)) ⟨j, hj⟩ =
    (PoweringTables.table input n).rows[i].relation[j]
  change rowAccept (fixedLabelAt d n) (rowBits input n (decodeDart vertices d n i))
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).1
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).2 = _
  rw [rowAccept_rowBits]
  exact h.symm

theorem rowBlock_unary_table (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (PoweringTables.dartCount vertices d n)) :
    encodeBits (List.ofFn (rowBlock (fixedLabelAt d n)
      (rowBits input n (decodeDart vertices d n i)))) =
      encodeWords (GenericGraphTables.relationWords (PoweringTables.table input n).rows[i].relation) := by
  rw [rowBlock_unary, emittedRelation_table]

/-- With the actual computed data on its input tape, the existing finite row
machine emits precisely the serialized relation of the actual output table.
The unread input suffix and prior output tape are preserved as specified. -/
def tableRowMachineInTime (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (PoweringTables.dartCount vertices d n)) (suffix : List Bool)
    (register : RowBuffer d n) (tapes : Bool → List Bool)
    (hinput : tapes false = dataTape input n (decodeDart vertices d n i) ++ suffix) :
    StateTransition.EvalsToInTime (PoweringMachineRow.machine (t := n + 1) (fixedLabelAt d n)).step
      ⟨some (), ((), register), tapes⟩
      (some ⟨none, ((), emptyBuffer (inputSize (n + 1) (slotCount d n))),
        Function.update (Function.update tapes false suffix) true
          (encodeWords (GenericGraphTables.relationWords
            (PoweringTables.table input n).rows[i].relation) ++ tapes true)⟩) 1 := by
  have hinput' : tapes false =
      encodeBits (List.ofFn (rowBits input n (decodeDart vertices d n i))) ++ suffix := by
    simpa only [dataTape_eq] using hinput
  have h := PoweringMachineRow.machineInTime (fixedLabelAt d n)
    (rowBits input n (decodeDart vertices d n i)) suffix register tapes hinput'
  simpa only [rowBlock_unary_table] using h

end UniqueGamesTheorem.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open UniqueGamesTheorem.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

/-- The actual ports before a selected time, with no vertex-dependent choice. -/
def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

theorem walkEnd_tailPorts (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
      walkEnd G v (tailPorts n p k) = (edgeAt G n (v, p) k).1 := by
  intro n
  induction n with
  | zero => intro v p k; rfl
  | succ n ih =>
      intro v p k
      refine Fin.cases rfl (fun j => ?_) k
      exact ih (next G v (p 0)) (fun i => p i.succ) j

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

theorem walkEnd_headPorts (G : PortGraph V D) (n : Nat) (v : V)
    (p : Fin (n + 1) → D) (k : Fin (n + 1)) :
    walkEnd G v (headPorts n p k) = (G.rot (edgeAt G n (v, p) k)).1 := by
  rw [headPorts, walkEnd_append, walkEnd_tailPorts]
  change (G.rot ((edgeAt G n (v, p) k).1, p k)).1 = _
  have hp : (edgeAt G n (v, p) k).2 = p k := edgeAt_port G n (v, p) k
  rw [← hp]

def addressPorts {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) : List (Fin d) :=
  List.ofFn ((allAddresses d t).get i).2

theorem walkEnd_addressPorts {d t : Nat} (G : PortGraph V (Fin d)) (v : V)
    (i : PoweringOpinionTables.AddressIndex d t) :
    walkEnd G v (addressPorts i) = (wordToBall G t v ((allAddresses d t).get i)).val :=
  (wordEnd_eq_walkEnd_ofFn G _ _ _).symm

/-- Static commands; all changing vertex identifiers remain inputs to evaluation. -/
inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

/-- The number of shared trajectory tapes needed by a single instruction. -/
def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

theorem addressPorts_length_le {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) :
    (addressPorts i).length ≤ t := by
  simp only [addressPorts, List.length_ofFn]
  exact Nat.le_of_lt_succ ((allAddresses d t).get i).1.isLt

def evaluate {vertices d : Nat} (input : PortTables.Table vertices d)
    (start : Fin vertices) : Instruction d → Bool
  | .relation ports port a b => PortTables.accepts input
      (walkEnd (PortTables.portGraph input) start ports, port) a b
  | .equal left right => decide
      (walkEnd (PortTables.portGraph input) start left =
        walkEnd (PortTables.portGraph input) start right)

def fieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) : Field (slotCount d n) → Instruction d
  | .inl (a, b) => .relation (tailPorts n ports k) (ports k) a b
  | .inr (.inl i) => .equal (addressPorts i) (tailPorts n ports k)
  | .inr (.inr i) => .equal (List.ofFn ports ++ addressPorts i) (headPorts n ports k)

theorem evaluate_fieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (fieldPlan n ports k field) = walkData input n (start, ports) k field := by
  rcases field with ⟨a,b⟩ | i | i
  · simp only [evaluate, fieldPlan, walkData, walkEnd_tailPorts]
    have hp : (edgeAt (PortTables.portGraph input) n (start, ports) k).2 = ports k :=
      edgeAt_port (PortTables.portGraph input) n (start, ports) k
    rw [← hp]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_tailPorts]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input) start i
    rw [ha]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_append,
      walkEnd_headPorts]
    rw [← wordEnd_eq_walkEnd_ofFn]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input)
      (wordEnd (PortTables.portGraph input) (n + 1) start ports) i
    rw [ha]
    rfl

def directedFieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) : Instruction d :=
  fieldPlan n ports k (if direction then transposeField field else field)

theorem fieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (fieldPlan n ports k field).radius ≤ 2 * (n + 1) := by
  have hk := k.isLt
  rcases field with ⟨a,b⟩ | i | i
  · simp only [fieldPlan, Instruction.radius, tailPorts_length]
    omega
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, tailPorts_length]
    exact max_le (by omega) (by omega)
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, headPorts, List.length_append,
      List.length_ofFn, List.length_singleton, tailPorts_length]
    exact max_le (by omega) (by omega)

theorem directedFieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (directedFieldPlan n ports direction k field).radius ≤ 2 * (n + 1) :=
  fieldPlan_radius n ports k _

theorem evaluate_directedFieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (directedFieldPlan n ports direction k field) =
      rowData input n (direction, start, ports) k field :=
  evaluate_fieldPlan input n start ports k _

/-- The exact fixed sequence of data-producing commands, in serialized order. -/
def rowPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Instruction d) :=
  List.ofFn fun i : Fin (inputSize (n + 1) (slotCount d n)) =>
    let pair := (inputEquiv (n + 1) (slotCount d n)).symm i
    directedFieldPlan n ports direction pair.1 pair.2

theorem evaluate_rowPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (rowPlan n ports direction).map (evaluate input start) =
      List.ofFn (rowBits input n (direction, start, ports)) := by
  rw [rowPlan, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [evaluate_directedFieldPlan, rowBits_packData]
  rfl

theorem dataTape_eq_plan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    dataTape input n (direction, start, ports) =
      encodeBits ((rowPlan n ports direction).map (evaluate input start)) := by
  rw [evaluate_rowPlan, dataTape_eq]

end UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open UniqueGamesTheorem.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

def reverseValue (d n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  blockSize d n * vertex.val + reverseOffset d n ports direction

def tailVertex (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Fin vertices :=
  if direction then wordEnd (PortTables.portGraph input) (n + 1) vertex ports else vertex

def headerWords (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  [(tailVertex input n vertex ports direction).val, reverseValue d n vertex ports direction]

/-- The stored tail is the recorded start or endpoint according to direction. -/
theorem table_tail (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n (direction, vertex, ports)].tail =
      tailVertex input n vertex ports direction := by
  change (GenericGraphTables.semantics (PoweringTables.table input n)).tail
    (encodeDart vertices d n (direction, vertex, ports)) = _
  rw [PoweringTables.semantics_table]
  change (PoweringTables.mathematicalGraph input n).tail
    ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, vertex, ports))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The reverse address retains the word and changes only its direction bit. -/
theorem table_reverseValue (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n
      (direction, vertex, ports)].reverseIndex.val = reverseValue d n vertex ports direction := by
  change (GenericGraphTables.reverseAt (PoweringTables.table input n).rows
    (encodeDart vertices d n (direction, vertex, ports))).val = _
  rw [PoweringTables.table_reverse, encodeDart, dartEquiv_val]
  cases direction <;>
    simp [reverseValue, blockSize, reverseOffset, orientationEquiv, Nat.add_assoc] <;> decide

theorem headerWords_eq (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    headerWords input n vertex ports direction =
      [(PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].tail.val,
       (PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].reverseIndex.val] := by
  rw [table_tail, table_reverseValue]
  rfl

/-- Prepending these two fields to the existing relation yields the exact
serialized row, preserving the rest of the output tape. -/
theorem header_relation_bits (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (suffix : List Bool) :
    encodeWords (headerWords input n vertex ports direction) ++
      (encodeWords (GenericGraphTables.relationWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)].relation) ++ suffix) =
      encodeWords (GenericGraphTables.rowWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)]) ++ suffix := by
  rw [headerWords_eq, ← List.append_assoc, ← encodeWords_append]
  rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
