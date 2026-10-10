import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTupleOdometer
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.ActualGame
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Reduction.ExplicitLemmas
import OAI.Computability.UniqueGames.Reduction.MachineFieldTemplate

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

inductive Token (k : Nat)
  | literal (value : Nat)
  | field (position : Fin k) (index : Fin 4)
  deriving DecidableEq, Repr

def evalToken (fields : Fin k → Fin 4 → Nat) : Token k → Nat
  | .literal value => value
  | .field position index => fields position index

def evalTemplate (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) : List Nat :=
  tokens.map (evalToken fields)

def nameField (j : Fin 3) : Fin 4 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def recordFields (names : Fin 3 → Nat) (occurrence : Nat) (i : Fin 4) : Nat :=
  if h : i.val < 3 then names ⟨i.val, h⟩ else occurrence

@[simp] theorem recordFields_name (names : Fin 3 → Nat) (occurrence : Nat) (j : Fin 3) :
    recordFields names occurrence (nameField j) = names j := by
  simp [recordFields, nameField, j.isLt]

@[simp] theorem recordFields_occurrence (names : Fin 3 → Nat) (occurrence : Nat) :
    recordFields names occurrence 3 = occurrence := by simp [recordFields]

def sourceFields {n m k : Nat} (occ : Fin k → Fin m) (names : Fin m → Fin 3 → Fin n)
    (j : Fin k) : Fin 4 → Nat :=
  recordFields (fun i => (names (occ j) i).val) (occ j).val

def liftToken (j : Fin k) : CanonicalWordTemplate.Token → Token k
  | .literal value => .literal value
  | .name index => .field j (nameField index)
  | .occurrence => .field j 3

def liftRecord (j : Fin k) (tokens : List CanonicalWordTemplate.Token) : List (Token k) :=
  tokens.map (liftToken j)

@[simp] theorem liftRecord_length (j : Fin k) (tokens : List CanonicalWordTemplate.Token) :
    (liftRecord j tokens).length = tokens.length := List.length_map _

theorem eval_liftToken {n m k : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (j : Fin k) (token : CanonicalWordTemplate.Token) :
    evalToken (sourceFields occ names) (liftToken j token) =
      CanonicalWordTemplate.evalToken (fun i => (names (occ j) i).val) (occ j).val token := by
  cases token <;> simp [evalToken, sourceFields, liftToken, CanonicalWordTemplate.evalToken]

theorem eval_liftRecord {n m k : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (j : Fin k)
    (tokens : List CanonicalWordTemplate.Token) :
    evalTemplate (sourceFields occ names) (liftRecord j tokens) =
      CanonicalWordTemplate.evalTemplate (fun i => (names (occ j) i).val) (occ j).val tokens := by
  simp only [evalTemplate, liftRecord, List.map_map, Function.comp_def, eval_liftToken,
    CanonicalWordTemplate.evalTemplate]

def recordsList {k s d : Nat} (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) : List (Token k) :=
  positions.flatMap (fun j => liftRecord j (CanonicalWordTemplate.template (a j)))

theorem recordsList_length {k s d : Nat} (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) : (recordsList a positions).length = 9 * positions.length := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    change (liftRecord j (CanonicalWordTemplate.template (a j)) ++
      recordsList a positions).length = 9 * (positions.length + 1)
    rw [List.length_append, liftRecord_length, CanonicalWordTemplate.template_length, ih]
    omega

theorem eval_recordsList {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) :
    evalTemplate (sourceFields occ names) (recordsList a positions) =
      (positions.map (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    change
      evalTemplate (sourceFields occ names)
          (liftRecord j (CanonicalWordTemplate.template (a j)) ++ recordsList a positions) =
        recordWords (ActualCanonical.record names (occ j) (a j)) ++
          (positions.map (fun i => ActualCanonical.record names (occ i) (a i))).flatMap recordWords
    rw [show ∀ xs ys, evalTemplate (sourceFields occ names) (xs ++ ys) =
      evalTemplate (sourceFields occ names) xs ++ evalTemplate (sourceFields occ names) ys by
      intro xs ys; exact List.map_append]
    rw [eval_liftRecord, CanonicalWordTemplate.eval_template, ih]

def ambientShift {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : Ambient s d :=
  z + ∑ j, b j • ActualCanonical.pivot (a j)

def alphabetOffset {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : Vector s :=
  (ambientShift z a b).1

def template {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : List (Token k) :=
  .literal (vectorWord (ambientShift z a b).2) :: recordsList a (List.ofFn id)

@[simp] theorem template_length {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) :
    (template z a b).length = 1 + 9*k := by
  simp [template, recordsList_length, Nat.add_comm]

/-- Exact body serialization of general canonical data. -/
theorem eval_data {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d) :
    evalTemplate (sourceFields occ names) (template z a (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.data occ names rhs z a).1.2,
        (ActualCanonical.data occ names rhs z a).2) := by
  change
    vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        evalTemplate (sourceFields occ names) (recordsList a (List.ofFn id)) =
      vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        (List.ofFn (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords
  rw [eval_recordsList, List.map_ofFn]
  rfl

theorem alphabetOffset_data {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d) :
    alphabetOffset z a (fun j => rhs (occ j)) =
      (ActualCanonical.data occ names rhs z a).1.1 := rfl

theorem eval_canonical {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (X : ActualHomogeneous.E k →ₗ[F2] Ambient s d) :
    evalTemplate (sourceFields occ names)
        (template (X (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple X)
          (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.canonical occ names rhs X).1.2,
        (ActualCanonical.canonical occ names rhs X).2) :=
  eval_data occ names rhs _ _

theorem alphabetOffset_canonical {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (X : ActualHomogeneous.E k →ₗ[F2] Ambient s d) :
    alphabetOffset (X (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple X)
        (fun j => rhs (occ j)) =
      (ActualCanonical.canonical occ names rhs X).1.1 := rfl

/-- The finite coefficient table's three coefficients for each local record. -/
def coefficientTriples {k s d : Nat} (c : ActualEnumeration.Coefficients k (Ambient s d))
    (j : Fin k) : Fin 3 → Ambient s d :=
  ![(c.2 j).1, (c.2 j).2, 0]

theorem fromCoefficients_hBasis {k s d : Nat}
    (c : ActualEnumeration.Coefficients k (Ambient s d)) :
    ActualEnumeration.fromCoefficients k (Ambient s d) c (ActualHomogeneous.hBasis k) = c.1 :=
  congrArg Prod.fst (ActualEnumeration.to_fromCoefficients k (Ambient s d) c)

theorem standardTriple_fromCoefficients {k s d : Nat}
    (c : ActualEnumeration.Coefficients k (Ambient s d)) :
    ActualCanonical.standardTriple (ActualEnumeration.fromCoefficients k (Ambient s d) c) =
      coefficientTriples c := by
  have h := ActualEnumeration.to_fromCoefficients k (Ambient s d) c
  funext j i
  fin_cases i
  · exact congrArg (fun p : ActualEnumeration.Coefficients k (Ambient s d) => (p.2 j).1) h
  · exact congrArg (fun p : ActualEnumeration.Coefficients k (Ambient s d) => (p.2 j).2) h
  · rfl

theorem eval_actualQuery (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    evalTemplate (sourceFields q.1 (ActualGame.names S))
        (template (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
          (fun j => ActualGame.rhs S (q.1 j))) =
      bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  eval_canonical q.1 (ActualGame.names S) (ActualGame.rhs S) q.2

theorem alphabetOffset_actualQuery (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    alphabetOffset (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
        (fun j => ActualGame.rhs S (q.1 j)) =
      ActualGame.offset S k s d q := rfl

/-- Direct specialization to an actual enumerated coefficient table. -/
theorem eval_fromCoefficients (S : ActualSource.Source) {k s d : Nat}
    (occ : ActualGame.Question S k) (c : ActualEnumeration.Coefficients k (Ambient s d)) :
    evalTemplate (sourceFields occ (ActualGame.names S))
        (template c.1 (coefficientTriples c) (fun j => ActualGame.rhs S (occ j))) =
      bodyWords (ActualOrbit.body (ActualGame.canonical S k s d)
        (occ, ActualEnumeration.fromCoefficients k (Ambient s d) c)) := by
  simpa only [fromCoefficients_hBasis, standardTriple_fromCoefficients] using
    eval_actualQuery S (occ, ActualEnumeration.fromCoefficients k (Ambient s d) c)

theorem alphabetOffset_fromCoefficients (S : ActualSource.Source) {k s d : Nat}
    (occ : ActualGame.Question S k) (c : ActualEnumeration.Coefficients k (Ambient s d)) :
    alphabetOffset c.1 (coefficientTriples c) (fun j => ActualGame.rhs S (occ j)) =
      ActualGame.offset S k s d
        (occ, ActualEnumeration.fromCoefficients k (Ambient s d) c) := by
  simpa only [fromCoefficients_hBasis, standardTriple_fromCoefficients] using
    alphabetOffset_actualQuery S (occ, ActualEnumeration.fromCoefficients k (Ambient s d) c)

/-- Both permutation offsets of an actual edge are the same finite expressions
used by the corresponding canonical-body templates. -/
theorem actualEdge_permutation (S : ActualSource.Source) (k : Nat) {s d : Nat}
    (g : ActualSource.SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    (ActualGame.edge S k g omega).permutation =
      Encoding.translationTable
        (alphabetOffset ((ActualGame.leftQuery S k g omega).2 (ActualHomogeneous.hBasis k))
          (ActualCanonical.standardTriple (ActualGame.leftQuery S k g omega).2)
          (fun j => ActualGame.rhs S ((ActualGame.leftQuery S k g omega).1 j)))
        (alphabetOffset ((ActualGame.rightQuery S k g omega).2 (ActualHomogeneous.hBasis k))
          (ActualCanonical.standardTriple (ActualGame.rightQuery S k g omega).2)
          (fun j => ActualGame.rhs S ((ActualGame.rightQuery S k g omega).1 j))) := rfl

theorem flatMap_encodeWord (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) :
    tokens.flatMap (fun token => encodeWord (evalToken fields token)) =
      encodeWords (evalTemplate fields tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons, evalTemplate, List.map_cons, encodeWords]
    exact congrArg (List.append (encodeWord (evalToken fields token))) ih

theorem actualQuery_bits (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (template (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
        (fun j => ActualGame.rhs S (q.1 j))).flatMap
          (fun token => encodeWord (evalToken (sourceFields q.1 (ActualGame.names S)) token)) =
      CanonicalEncoding.bodyBits (ActualOrbit.body (ActualGame.canonical S k s d) q) := by
  rw [flatMap_encodeWord, eval_actualQuery]
  rfl

end UniqueGamesTheorem.Reduction.CanonicalBodyTemplate

end

section

/-! Lower a complete canonical-body template to the actual field-template
machine. There are four saved fields per query position, numbered by
`field + 4 * position`. The template constants depend only on finite coefficient
and RHS data; names and occurrence identifiers remain saved tape contents. -/

namespace UniqueGamesTheorem.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

def fieldEquiv (k : Nat) : (Fin k × Fin 4) ≃ Fin (4*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 4))

def fieldIndex (position : Fin k) (field : Fin 4) : Fin (4*k) :=
  fieldEquiv k (position, field)

@[simp] theorem fieldIndex_val (position : Fin k) (field : Fin 4) :
    (fieldIndex position field).val = field.val + 4 * position.val := rfl

def savedFields (fields : Fin k → Fin 4 → Nat) (index : Fin (4*k)) : List Bool :=
  encodeWord (fields ((fieldEquiv k).symm index).1 ((fieldEquiv k).symm index).2)

@[simp] theorem savedFields_fieldIndex (fields : Fin k → Fin 4 → Nat)
    (position : Fin k) (field : Fin 4) :
    savedFields fields (fieldIndex position field) = encodeWord (fields position field) := by
  simp [savedFields, fieldIndex]

def lowerToken : CanonicalBodyTemplate.Token k → MachineFieldTemplate.Token (4*k)
  | .literal value => .literal (encodeWord value)
  | .field position field => .copy (fieldIndex position field)

def lowerTemplate (tokens : List (CanonicalBodyTemplate.Token k)) :
    List (MachineFieldTemplate.Token (4*k)) := tokens.map lowerToken

@[simp] theorem lowerTemplate_length (tokens : List (CanonicalBodyTemplate.Token k)) :
    (lowerTemplate tokens).length = tokens.length := List.length_map _

theorem tokenOutput_lowerToken (fields : Fin k → Fin 4 → Nat)
    (token : CanonicalBodyTemplate.Token k) :
    MachineFieldTemplate.tokenOutput (savedFields fields) (lowerToken token) =
      encodeWord (CanonicalBodyTemplate.evalToken fields token) := by
  cases token <;>
    simp [lowerToken, MachineFieldTemplate.tokenOutput, CanonicalBodyTemplate.evalToken]

theorem templateOutput_lowerTemplate (fields : Fin k → Fin 4 → Nat)
    (tokens : List (CanonicalBodyTemplate.Token k)) :
    MachineFieldTemplate.templateOutput (lowerTemplate tokens) (savedFields fields) =
      encodeWords (CanonicalBodyTemplate.evalTemplate fields tokens) := by
  simp only [MachineFieldTemplate.templateOutput, lowerTemplate, List.flatMap_map,
    tokenOutput_lowerToken]
  exact CanonicalBodyTemplate.flatMap_encodeWord fields tokens

/-- This fixed token list is directly accepted by the actual template machine. -/
def template {k s d : Nat} (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d)
    (b : Fin k → F2) : List (MachineFieldTemplate.Token (4*k)) :=
  lowerTemplate (CanonicalBodyTemplate.template z a b)

@[simp] theorem template_length {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) :
    (template z a b).length = 1 + 9*k := by
  simp [template]

theorem templateOutput_data {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d) :
    MachineFieldTemplate.templateOutput (template z a (fun j => rhs (occ j)))
        (savedFields (CanonicalBodyTemplate.sourceFields occ names)) =
      encodeWords (bodyWords ((ActualCanonical.data occ names rhs z a).1.2,
        (ActualCanonical.data occ names rhs z a).2)) := by
  rw [template, templateOutput_lowerTemplate, CanonicalBodyTemplate.eval_data]

theorem templateOutput_actualQuery (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    MachineFieldTemplate.templateOutput
        (template (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
          (fun j => ActualGame.rhs S (q.1 j)))
        (savedFields (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S))) =
      encodeWords (bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q)) := by
  rw [template, templateOutput_lowerTemplate, CanonicalBodyTemplate.eval_actualQuery]

/-- Exact output using the finite coefficient table directly as program data. -/
theorem templateOutput_fromCoefficients (S : ActualSource.Source) {k s d : Nat}
    (occ : ActualGame.Question S k) (c : ActualEnumeration.Coefficients k (Ambient s d)) :
    MachineFieldTemplate.templateOutput
        (template c.1 (CanonicalBodyTemplate.coefficientTriples c)
          (fun j => ActualGame.rhs S (occ j)))
        (savedFields (CanonicalBodyTemplate.sourceFields occ (ActualGame.names S))) =
      encodeWords (bodyWords (ActualOrbit.body (ActualGame.canonical S k s d)
        (occ, ActualEnumeration.fromCoefficients k (Ambient s d) c))) := by
  rw [template, templateOutput_lowerTemplate, CanonicalBodyTemplate.eval_fromCoefficients]

end UniqueGamesTheorem.Reduction.CanonicalBodyMachine

end

section

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace UniqueGamesTheorem.Reduction.OccurrenceTupleOrder

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

/-- Read the physical saved digit positions in reverse coordinate order. -/
def readCoordinates {m k : Nat} (digits : Fin k → Fin m) : Fin k → Fin m :=
  digits ∘ Fin.rev

@[simp] theorem readCoordinates_apply {m k : Nat} (digits : Fin k → Fin m) (j : Fin k) :
    readCoordinates digits j = digits j.rev := rfl

@[simp] theorem readCoordinates_involutive {m k : Nat} (digits : Fin k → Fin m) :
    readCoordinates (readCoordinates digits) = digits := by
  funext j
  simp only [readCoordinates_apply, Fin.rev_rev]

def coordinateEquiv (m k : Nat) : (Fin k → Fin m) ≃ (Fin k → Fin m) where
  toFun := readCoordinates
  invFun := readCoordinates
  left_inv := readCoordinates_involutive
  right_inv := readCoordinates_involutive

theorem readCoordinates_snoc {m k : Nat} (tail : Fin k → Fin m) (d : Fin m) :
    readCoordinates (Fin.snoc tail d) = Fin.cons d (readCoordinates tail) :=
  Fin.snoc_comp_rev d tail

/-- Exact equality of occurrence lists after reading saved digits in reverse
coordinate order. This includes dimension zero and radix zero. -/
theorem tupleOrder_readCoordinates (m k : Nat) :
    (MachineTupleOdometer.tupleOrder m k).map readCoordinates =
      ActualEnumeration.functions (List.finRange m) k := by
  induction k with
  | zero =>
    rw [MachineTupleOdometer.tupleOrder_dimension_zero]
    change [readCoordinates (fun i : Fin 0 => Fin.elim0 i)] = [Fin.elim0]
    congr 1
  | succ k ih =>
    have each (d : Fin m) :
        ((MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d)).map
          readCoordinates =
        (ActualEnumeration.functions (List.finRange m) k).map (Fin.cons d) := by
      calc
        _ = ((MachineTupleOdometer.tupleOrder m k).map readCoordinates).map (Fin.cons d) := by
          simp only [List.map_map, Function.comp_def, readCoordinates_snoc]
        _ = _ := by rw [ih]
    rw [MachineTupleOdometer.tupleOrder_snoc]
    change ((List.finRange m).flatMap (fun d =>
      (MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d))).map
      readCoordinates = _
    simp only [List.map_flatMap, each]
    simp only [ActualEnumeration.functions, Explicit.pairs, List.map_flatMap,
      List.map_map, Function.comp_def]

theorem functions_readCoordinates (m k : Nat) :
    (ActualEnumeration.functions (List.finRange m) k).map readCoordinates =
      MachineTupleOdometer.tupleOrder m k := by
  have h := congrArg (List.map readCoordinates) (tupleOrder_readCoordinates m k)
  simpa only [List.map_map, Function.comp_def, readCoordinates_involutive,
    List.map_id_fun', id_eq] using h.symm

/-- An arbitrary exact emitted list, including serialized edge bytes, inherits
the order identity. There is no permutation or counting-only replacement. -/
theorem functions_flatMap (m k : Nat) (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      (MachineTupleOdometer.tupleOrder m k).flatMap
        (fun digits => emit (readCoordinates digits)) := by
  rw [← tupleOrder_readCoordinates]
  exact List.flatMap_map readCoordinates emit _

section ActualSchedule

variable {K Λ σ : Type} [DecidableEq K]
  {m k : Nat} {current remaining : Nat → K} {bodyLabel : Λ}
  {checkLabel resetLabel : Nat → Λ}
  {program : Λ → TM2.Stmt (MachineTupleOdometer.Alphabet (K := K)) Λ (σ × Option Bool)}
  {exitLabel : Λ} {start finish : MachineTupleOdometer.Configuration K Λ σ}

/-- Apply the coordinate readout to an existing actual odometer schedule.
Its visit-order theorem already follows from the real nested-cycle constructors. -/
theorem actualSchedule_order
    (tree : MachineTupleOdometer.NestedCycle m current remaining bodyLabel
      checkLabel resetLabel program k exitLabel start finish) :
    tree.order.map readCoordinates = ActualEnumeration.functions (List.finRange m) k := by
  rw [MachineTupleOdometer.NestedCycle.order_eq_tupleOrder, tupleOrder_readCoordinates]

theorem actualSchedule_flatMap
    (tree : MachineTupleOdometer.NestedCycle m current remaining bodyLabel
      checkLabel resetLabel program k exitLabel start finish)
    (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      tree.order.flatMap (fun digits => emit (readCoordinates digits)) := by
  rw [MachineTupleOdometer.NestedCycle.order_eq_tupleOrder]
  exact functions_flatMap m k emit

end ActualSchedule

end UniqueGamesTheorem.Reduction.OccurrenceTupleOrder

end

section

/-! An occurrence-preserving E3LIN table codec. The word stream contains its
declared variable count and equation count, followed by four words per equation.
Parsing checks all three indices, the Boolean right-hand side, the exact count,
absence of trailing words, and nonemptiness. Length theorems below concern the
actual serialized output; they make no running-time claim. -/

namespace UniqueGamesTheorem.Reduction.SourceEncoding

open UniqueGamesTheorem.Foundations.Complexity

structure Input where
  «variables» : Nat
  equations : List (CloneGap.Equation (Fin «variables»))
  nonempty : equations ≠ []

abbrev Table := Input

def equationWords {n : Nat} (e : CloneGap.Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (input : Input) : List Nat :=
  [input.variables, input.equations.length] ++ input.equations.flatMap equationWords

def inputBits (input : Input) : List Bool := encodeWords (inputWords input)

def parseEquation («variables» : Nat) :
    List Nat → Option (CloneGap.Equation (Fin «variables») × List Nat)
  | first :: second :: third :: rhs :: rest =>
      if hfirst : first < «variables» then
        if hsecond : second < «variables» then
          if hthird : third < «variables» then
            if rhs = 0 then
              some (⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, ⟨third, hthird⟩, false⟩, rest)
            else if rhs = 1 then
              some (⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, ⟨third, hthird⟩, true⟩, rest)
            else none
          else none
        else none
      else none
  | _ => none

@[simp] theorem parseEquation_encoded {n : Nat} (e : CloneGap.Equation (Fin n))
    (rest : List Nat) :
    parseEquation n (equationWords e ++ rest) = some (e, rest) := by
  cases e with
  | mk first second third rhs =>
      cases rhs <;> simp [equationWords, parseEquation, first.isLt, second.isLt, third.isLt]

def parseEquations («variables» : Nat) :
    Nat → List Nat → Option (List (CloneGap.Equation (Fin «variables»)) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (equation, words) ← parseEquation «variables» words
      let (equations, words) ← parseEquations «variables» count words
      return (equation :: equations, words)

/-- Parsing preserves the entire ordered list, including all equal entries. -/
@[simp] theorem parseEquations_encoded {n : Nat}
    (equations : List (CloneGap.Equation (Fin n))) (rest : List Nat) :
    parseEquations n equations.length (equations.flatMap equationWords ++ rest) =
      some (equations, rest) := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp [List.append_assoc, parseEquations, parseEquation_encoded, ih]

def decodeInputWords : List Nat → Option Input
  | «variables» :: count :: words => do
      let (equations, trailing) ← parseEquations «variables» count words
      if trailing = [] then
        if nonempty : 0 < equations.length then
          some ⟨«variables», equations, List.length_pos_iff.mp nonempty⟩
        else none
      else none
  | _ => none

@[simp] theorem decodeInputWords_encoded (input : Input) :
    decodeInputWords (inputWords input) = some input := by
  cases input with
  | mk «variables» equations nonempty =>
      have parsed := parseEquations_encoded equations []
      have positive := List.length_pos_iff.mpr nonempty
      simp only [List.append_nil] at parsed
      simp [decodeInputWords, inputWords, parsed, positive]

def decodeInputBits (bits : List Bool) : Option Input :=
  decodeWords bits >>= decodeInputWords

@[simp] theorem decodeInputBits_encoded (input : Input) :
    decodeInputBits (inputBits input) = some input := by
  simp [decodeInputBits, inputBits]

theorem inputWords_injective {first second : Input}
    (same : inputWords first = inputWords second) : first = second := by
  have parsed := congrArg decodeInputWords same
  simpa only [decodeInputWords_encoded, Option.some.injEq] using parsed

theorem inputBits_injective {first second : Input}
    (same : inputBits first = inputBits second) : first = second := by
  have parsed := congrArg decodeInputBits same
  simpa only [decodeInputBits_encoded, Option.some.injEq] using parsed

@[simp] theorem equationWords_length {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (equationWords e).length = 4 := by simp [equationWords]

theorem equationsWords_length {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (equations.flatMap equationWords).length = 4 * equations.length := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp only [List.flatMap_cons, List.length_append, equationWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem inputWords_length (input : Input) :
    (inputWords input).length = 2 + 4 * input.equations.length := by
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    equationsWords_length]

theorem equationBits_length_le {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (encodeWords (equationWords e)).length ≤ 3 * n + 2 := by
  have hfirst := e.first.isLt
  have hsecond := e.second.isLt
  have hthird := e.third.isLt
  cases hrhs : e.rhs <;> simp [equationWords, hrhs] <;> omega

theorem equationsBits_length_le {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (encodeWords (equations.flatMap equationWords)).length ≤
      equations.length * (3 * n + 2) := by
  induction equations with
  | nil => simp [encodeWords]
  | cons e equations ih =>
      have he := equationBits_length_le e
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.variables + input.equations.length + 2 +
      (encodeWords (input.equations.flatMap equationWords)).length := by
  simp only [inputBits, inputWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem inputBits_length_le (input : Input) :
    (inputBits input).length ≤ input.variables + input.equations.length + 2 +
      input.equations.length * (3 * input.variables + 2) := by
  rw [inputBits_length]
  exact Nat.add_le_add_left (equationsBits_length_le input.equations) _

theorem inputBits_length_ge_variables (input : Input) :
    input.variables ≤ (inputBits input).length := by rw [inputBits_length]; omega

theorem inputBits_length_ge_equations (input : Input) :
    input.equations.length ≤ (inputBits input).length := by rw [inputBits_length]; omega

end UniqueGamesTheorem.Reduction.SourceEncoding

end

end OAI
