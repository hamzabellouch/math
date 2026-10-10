import Mathlib
import OAI.Computability.MaxCut.Encoding.TableKeysCompleteness

namespace OAI

namespace MaxCutGames.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

/-- A literal word or a reference to one of the four saved input fields. -/
inductive Token
  | literal (value : Nat)
  | name (index : Fin 3)
  | occurrence
  deriving DecidableEq, Repr

def evalToken (names : Fin 3 → Nat) (occurrence : Nat) : Token → Nat
  | .literal value => value
  | .name index => names index
  | .occurrence => occurrence

def evalTemplate (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : List Nat :=
  tokens.map (evalToken names occurrence)

def isVariable : Token → Bool
  | .literal _ => false
  | .name _ => true
  | .occurrence => true

def variableTokens (tokens : List Token) : List Token := tokens.filter isVariable

def blankTemplate : List Token :=
  [.literal 0, .literal 0, .literal 0, .literal 0, .literal 0,
    .literal 0, .literal 0, .literal 0, .literal 0]

def singleTemplate {s d : Nat} (index : Fin 3) (coefficient : Ambient s d) : List Token :=
  [.literal 1, .name index, .literal 0,
    .literal (vectorWord coefficient.1), .literal (vectorWord coefficient.2),
    .literal 0, .literal 0, .literal 0, .literal 0]

def fullTemplate {s d : Nat} (coefficients : Fin 3 → Ambient s d) : List Token :=
  [.literal 2, .literal 0, .occurrence,
    .literal (vectorWord (coefficients 0).1), .literal (vectorWord (coefficients 0).2),
    .literal (vectorWord (coefficients 1).1), .literal (vectorWord (coefficients 1).2),
    .literal (vectorWord (coefficients 2).1), .literal (vectorWord (coefficients 2).2)]

/-- Coefficient equality alone selects the record tag and the input field. -/
def template {s d : Nat} (a : Fin 3 → Ambient s d) : List Token :=
  if a 0 = a 1 then
    if a 0 = a 2 then blankTemplate else singleTemplate 2 (a 2 + a 0)
  else if a 0 = a 2 then singleTemplate 1 (a 1 + a 0)
  else if a 1 = a 2 then singleTemplate 0 (a 0 + a 2)
  else fullTemplate (ActualCanonical.normalize a)

@[simp] theorem blankTemplate_length : blankTemplate.length = 9 := rfl

@[simp] theorem singleTemplate_length {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) : (singleTemplate index coefficient).length = 9 := rfl

@[simp] theorem fullTemplate_length {s d : Nat} (coefficients : Fin 3 → Ambient s d) :
    (fullTemplate coefficients).length = 9 := rfl

@[simp] theorem template_length {s d : Nat} (a : Fin 3 → Ambient s d) :
    (template a).length = 9 := by
  unfold template
  split_ifs <;> rfl

@[simp] theorem evalTemplate_length (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : (evalTemplate names occurrence tokens).length = tokens.length :=
  List.length_map _

theorem eval_blankTemplate {n m s d : Nat} (names : Fin 3 → Fin n) (occurrence : Fin m) :
    evalTemplate (fun j => (names j).val) occurrence.val blankTemplate =
      recordWords (ActualCanonical.Record.blank : Record n m s d) := rfl

theorem eval_singleTemplate {n m s d : Nat} (names : Fin 3 → Fin n) (occurrence : Fin m)
    (index : Fin 3) (coefficient : Ambient s d) :
    evalTemplate (fun j => (names j).val) occurrence.val (singleTemplate index coefficient) =
      recordWords (ActualCanonical.Record.single (names index) coefficient : Record n m s d) :=
  rfl

theorem eval_fullTemplate {n m s d : Nat} (names : Fin 3 → Fin n) (occurrence : Fin m)
    (coefficients : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names j).val) occurrence.val (fullTemplate coefficients) =
      recordWords (ActualCanonical.Record.full occurrence coefficients : Record n m s d) :=
  rfl

/-- The template evaluates to the exact existing canonical-record encoding. -/
theorem eval_template {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names occurrence j).val) occurrence.val (template a) =
      recordWords (ActualCanonical.record names occurrence a) := by
  unfold template ActualCanonical.record
  split_ifs <;> rfl

@[simp] theorem variableTokens_blankTemplate : variableTokens blankTemplate = [] := rfl

@[simp] theorem variableTokens_singleTemplate {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) :
    variableTokens (singleTemplate index coefficient) = [.name index] := rfl

@[simp] theorem variableTokens_fullTemplate {s d : Nat}
    (coefficients : Fin 3 → Ambient s d) :
    variableTokens (fullTemplate coefficients) = [.occurrence] := rfl

/-- Exact input-field profile: blank has none; single reads one selected name;
full reads the occurrence identifier. Coefficient values are program constants. -/
theorem variableTokens_template {s d : Nat} (a : Fin 3 → Ambient s d) :
    variableTokens (template a) =
      if a 0 = a 1 then
        if a 0 = a 2 then [] else [.name 2]
      else if a 0 = a 2 then [.name 1]
      else if a 1 = a 2 then [.name 0]
      else [.occurrence] := by
  unfold template
  split_ifs <;> rfl

theorem variableTokens_template_length_le_one {s d : Nat} (a : Fin 3 → Ambient s d) :
    (variableTokens (template a)).length ≤ 1 := by
  rw [variableTokens_template]
  split_ifs <;> simp

theorem name_mem_variableTokens_iff {s d : Nat} (a : Fin 3 → Ambient s d) (index : Fin 3) :
    Token.name index ∈ variableTokens (template a) ↔
      (a 0 = a 1 ∧ a 0 ≠ a 2 ∧ index = 2) ∨
      (a 0 ≠ a 1 ∧ a 0 = a 2 ∧ index = 1) ∨
      (a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 = a 2 ∧ index = 0) := by
  by_cases h01 : a 0 = a 1 <;> by_cases h02 : a 0 = a 2 <;>
    by_cases h12 : a 1 = a 2 <;> simp [variableTokens_template, h01, h02, h12]

theorem occurrence_mem_variableTokens_iff {s d : Nat} (a : Fin 3 → Ambient s d) :
    Token.occurrence ∈ variableTokens (template a) ↔
      a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 ≠ a 2 := by
  by_cases h01 : a 0 = a 1 <;> by_cases h02 : a 0 = a 2 <;>
    by_cases h12 : a 1 = a 2 <;> simp [variableTokens_template, h01, h02, h12]

/-- Emitting each token's existing unary-delimited word gives exactly the
existing list-of-words serialization, with no alternative encoding. -/
theorem flatMap_encodeWord (names : Fin 3 → Nat) (occurrence : Nat) (tokens : List Token) :
    tokens.flatMap (fun token => encodeWord (evalToken names occurrence token)) =
      encodeWords (evalTemplate names occurrence tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons, evalTemplate, List.map_cons, encodeWords]
    exact congrArg (List.append (encodeWord (evalToken names occurrence token))) ih

theorem template_bits {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    (template a).flatMap
        (fun token => encodeWord (evalToken (fun j => (names occurrence j).val)
          occurrence.val token)) =
      encodeWords (recordWords (ActualCanonical.record names occurrence a)) := by
  rw [flatMap_encodeWord, eval_template]

end MaxCutGames.Reduction.CanonicalWordTemplate

namespace MaxCutGames.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

inductive Token (k : Nat)
  | literal (value : Nat)
  | field (position : Fin k) (index : Fin 4)
  deriving DecidableEq, Repr

variable {k : Nat}

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

end MaxCutGames.Reduction.CanonicalBodyTemplate

end OAI
