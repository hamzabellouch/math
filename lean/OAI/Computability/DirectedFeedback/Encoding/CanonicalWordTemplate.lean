import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineAddressHeaders
import OAI.Computability.DirectedFeedback.Machines.MachineTemplateAddress

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

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

end DFVSGames.Reduction.CanonicalWordTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyTemplate

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

end DFVSGames.Reduction.CanonicalBodyTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyMachine

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

theorem templateOutput_fromCoefficients (S : ActualSource.Source) {k s d : Nat}
    (occ : ActualGame.Question S k) (c : ActualEnumeration.Coefficients k (Ambient s d)) :
    MachineFieldTemplate.templateOutput
        (template c.1 (CanonicalBodyTemplate.coefficientTriples c)
          (fun j => ActualGame.rhs S (occ j)))
        (savedFields (CanonicalBodyTemplate.sourceFields occ (ActualGame.names S))) =
      encodeWords (bodyWords (ActualOrbit.body (ActualGame.canonical S k s d)
        (occ, ActualEnumeration.fromCoefficients k (Ambient s d) c))) := by
  rw [template, templateOutput_lowerTemplate, CanonicalBodyTemplate.eval_fromCoefficients]

end DFVSGames.Reduction.CanonicalBodyMachine
end

section

namespace DFVSGames.Reduction.AddressMachineSpace

open DFVSGames.Foundations.Complexity

abbrev Extra (k s d noiseCount : Nat) :=
  MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ⊕
    (MachineTemplateAddress.Tape (4 * k) (1 + 9 * k) ⊕ (Fin k ⊕ Unit))

abbrev Tape (k s d noiseCount : Nat) :=
  MachineSourceTuple.Tape k (Extra k s d noiseCount)

abbrev Control (k : Nat) := ((Fin k → Bool) × Unit) × Unit
abbrev State (k : Nat) := Control k × Option Bool

def initialState (k : Nat) : State k := (((fun _ => false, ()), ()), none)

variable (k s d noiseCount : Nat)

def headerArithmeticSlots : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ↪
    Tape k s d noiseCount where
  toFun a := .extra (.inl a)
  inj' := by intro a b h; exact Sum.inl.inj (MachineSourceTuple.Tape.extra.inj h)

def headerTape (c : MachineAddressHeaders.Arithmetic.Control) : Tape k s d noiseCount :=
  .extra (.inl (.inl c))

@[simp] theorem headerTape_eq_iff (a b : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount a = headerTape k s d noiseCount b ↔ a = b := by
  simp [headerTape]

def fullHeaderSlots : MachineAddressHeaders.Layout k s d noiseCount ↪ Tape k s d noiseCount where
  toFun
    | .inl 0 => .source
    | .inl 1 => .work
    | .inr a => headerArithmeticSlots k s d noiseCount a
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> cases h <;> rfl
    · fin_cases a <;> cases h
    · fin_cases b <;> cases h
    · exact congrArg Sum.inr ((headerArithmeticSlots k s d noiseCount).injective h)

@[simp] theorem fullHeaderSlots_source : fullHeaderSlots k s d noiseCount (.inl 0) = .source := rfl
@[simp] theorem fullHeaderSlots_work : fullHeaderSlots k s d noiseCount (.inl 1) = .work := rfl
@[simp] theorem fullHeaderSlots_arithmetic (a : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount) :
    fullHeaderSlots k s d noiseCount (.inr a) = headerArithmeticSlots k s d noiseCount a := rfl

@[simp] theorem arithmeticSlots_fullHeaderSlots :
    MachineAddressHeaders.arithmeticSlots (fullHeaderSlots k s d noiseCount) =
      headerArithmeticSlots k s d noiseCount := by ext a; rfl

def prefixSlots : Fin 5 ↪ Tape k s d noiseCount :=
  MachineAddressHeaders.prefixSlots (fullHeaderSlots k s d noiseCount)

@[simp] theorem prefixSlots_source : prefixSlots k s d noiseCount 0 = .source := rfl
@[simp] theorem prefixSlots_work : prefixSlots k s d noiseCount 1 = .work := rfl
@[simp] theorem prefixSlots_variables :
    prefixSlots k s d noiseCount 2 = headerTape k s d noiseCount .variableCount := rfl
@[simp] theorem prefixSlots_occurrences :
    prefixSlots k s d noiseCount 3 = headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem prefixSlots_scratch :
    prefixSlots k s d noiseCount 4 = headerTape k s d noiseCount .scratch := rfl

def canonicalField (position : Fin k) (slot : Fin 4) : Tape k s d noiseCount :=
  if slot = 3 then .savedIndex position else .field position slot

def rhsField (position : Fin k) : Tape k s d noiseCount := .field position 3

@[simp] theorem canonicalField_occurrence (position : Fin k) :
    canonicalField k s d noiseCount position 3 = .savedIndex position := by simp [canonicalField]

@[simp] theorem canonicalField_name (position : Fin k) (slot : Fin 3) :
    canonicalField k s d noiseCount position (MachineSourceTuple.nameSlot slot) =
      MachineSourceTuple.nameField position slot := by
  have hs : MachineSourceTuple.nameSlot slot ≠ (3 : Fin 4) := by
    intro h
    have hv := congrArg Fin.val h
    have bound := slot.isLt
    simp only [MachineSourceTuple.nameSlot] at hv
    omega
  simp [canonicalField, hs, MachineSourceTuple.nameField]

theorem canonicalField_ne_rhsField (position other : Fin k) (slot : Fin 4) :
    canonicalField k s d noiseCount position slot ≠ rhsField k s d noiseCount other := by
  by_cases h : slot = 3 <;> simp [canonicalField, rhsField, h]

def privateAddress (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    Tape k s d noiseCount := .extra (.inr (.inl tape))

def edgeSlot : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) → Tape k s d noiseCount
  | .inl (.field i) => canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2
  | .inl .radix => headerTape k s d noiseCount .baseValue
  | .inl tape => privateAddress k s d noiseCount tape
  | .inr i => if i = 0 then headerTape k s d noiseCount .capacity
      else headerTape k s d noiseCount .reversed

private def edgeDecode_inline_AddressMachineSpace : Tape k s d noiseCount →
    Option (MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
  | .savedIndex j => some (.inl (.field (CanonicalBodyMachine.fieldIndex j 3)))
  | .field j slot => if slot = 3 then none
      else some (.inl (.field (CanonicalBodyMachine.fieldIndex j slot)))
  | .extra (.inl (.inl .baseValue)) => some (.inl .radix)
  | .extra (.inl (.inl .capacity)) => some (.inr 0)
  | .extra (.inl (.inl .reversed)) => some (.inr 1)
  | .extra (.inr (.inl tape)) => some (.inl tape)
  | _ => none

private theorem edgeDecode_canonicalField_inline_AddressMachineSpace (position : Fin k) (slot : Fin 4) :
    edgeDecode_inline_AddressMachineSpace k s d noiseCount (canonicalField k s d noiseCount position slot) =
      some (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) := by
  by_cases h : slot = 3 <;> simp [canonicalField, edgeDecode_inline_AddressMachineSpace, h]

private theorem edgeDecode_edgeSlot_inline_AddressMachineSpace (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    edgeDecode_inline_AddressMachineSpace k s d noiseCount (edgeSlot k s d noiseCount tape) = some tape := by
  rcases tape with tape | i
  · cases tape <;> try rfl
    rename_i index
    rw [edgeSlot, edgeDecode_canonicalField_inline_AddressMachineSpace]
    exact congrArg (fun i => some (Sum.inl (MachineTemplateAddress.Tape.field i)))
      ((CanonicalBodyMachine.fieldEquiv k).apply_symm_apply index)
  · fin_cases i <;> rfl

def addressEdgeSlots : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) ↪ Tape k s d noiseCount where
  toFun := edgeSlot k s d noiseCount
  inj' := by
    intro a b h
    have decoded := congrArg (edgeDecode_inline_AddressMachineSpace k s d noiseCount) h
    apply Option.some.inj
    simpa only [edgeDecode_edgeSlot_inline_AddressMachineSpace] using decoded

@[simp] theorem addressEdgeSlots_fieldIndex (position : Fin k) (slot : Fin 4) :
    addressEdgeSlots k s d noiseCount
      (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) =
        canonicalField k s d noiseCount position slot := by
  change canonicalField k s d noiseCount
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).1
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).2 = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem addressSlots_name (position : Fin k) (slot : Fin 3) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position (MachineSourceTuple.nameSlot slot))) =
        MachineSourceTuple.nameField position slot := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position _).trans
    (canonicalField_name k s d noiseCount position slot)

@[simp] theorem addressSlots_occurrence (position : Fin k) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position 3)) = .savedIndex position := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position 3).trans
    (canonicalField_occurrence k s d noiseCount position)

@[simp] theorem addressSlots_radix :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount) .radix =
      headerTape k s d noiseCount .baseValue := rfl
@[simp] theorem addressSlots_capacity :
    MachineAddressEdge.capacityTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .capacity := rfl
@[simp] theorem addressSlots_output :
    MachineAddressEdge.outputTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .reversed := rfl

def current (j : Fin k) : Tape k s d noiseCount := .savedIndex j.rev
def remaining (j : Fin k) : Tape k s d noiseCount := .extra (.inr (.inr (.inl j)))
def finalOutput : Tape k s d noiseCount := .extra (.inr (.inr (.inr ())))

@[simp] theorem current_rev (j : Fin k) : current k s d noiseCount j.rev = .savedIndex j := by
  simp [current]

def odometerSlots : MachineOdometerInit.Tape k ↪ Tape k s d noiseCount where
  toFun
    | .radix => headerTape k s d noiseCount .occurrenceCount
    | .scratch => .copyScratch
    | .current j => current k s d noiseCount j
    | .remaining j => remaining k s d noiseCount j
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [headerTape, current, remaining]

@[simp] theorem odometerSlots_radix : odometerSlots k s d noiseCount .radix =
    headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem odometerSlots_scratch : odometerSlots k s d noiseCount .scratch = .copyScratch := rfl
@[simp] theorem odometerSlots_current (j : Fin k) :
    odometerSlots k s d noiseCount (.current j) = .savedIndex j.rev := rfl
@[simp] theorem odometerSlots_remaining (j : Fin k) :
    odometerSlots k s d noiseCount (.remaining j) = remaining k s d noiseCount j := rfl

theorem current_ne_remaining (j l : Fin k) :
    current k s d noiseCount j ≠ remaining k s d noiseCount l := by simp [current, remaining]
theorem current_ne_finalOutput (j : Fin k) :
    current k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [current, finalOutput]
theorem remaining_ne_finalOutput (j : Fin k) :
    remaining k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [remaining, finalOutput]

private theorem edgeSlot_ne_of_decode_none_inline_AddressMachineSpace
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) (p : Tape k s d noiseCount)
    (h : edgeDecode_inline_AddressMachineSpace k s d noiseCount p = none) : edgeSlot k s d noiseCount tape ≠ p := by
  intro same
  have decoded := congrArg (edgeDecode_inline_AddressMachineSpace k s d noiseCount) same
  rw [edgeDecode_edgeSlot_inline_AddressMachineSpace, h] at decoded
  cases decoded

theorem addressEdgeSlots_ne_rhsField
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) (j : Fin k) :
    addressEdgeSlots k s d noiseCount tape ≠ rhsField k s d noiseCount j :=
  edgeSlot_ne_of_decode_none_inline_AddressMachineSpace k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_source
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    addressEdgeSlots k s d noiseCount tape ≠ .source :=
  edgeSlot_ne_of_decode_none_inline_AddressMachineSpace k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_copyScratch
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    addressEdgeSlots k s d noiseCount tape ≠ .copyScratch :=
  edgeSlot_ne_of_decode_none_inline_AddressMachineSpace k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_headerTape
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
    (c : MachineAddressHeaders.Arithmetic.Control)
    (hb : c ≠ .baseValue) (hc : c ≠ .capacity) (hr : c ≠ .reversed) :
    addressEdgeSlots k s d noiseCount tape ≠ headerTape k s d noiseCount c := by
  apply edgeSlot_ne_of_decode_none_inline_AddressMachineSpace
  cases c <;> simp_all [edgeDecode_inline_AddressMachineSpace, headerTape]

theorem addressEdgeSlots_ne_remaining
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) (j : Fin k) :
    addressEdgeSlots k s d noiseCount tape ≠ remaining k s d noiseCount j :=
  edgeSlot_ne_of_decode_none_inline_AddressMachineSpace k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_finalOutput
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    addressEdgeSlots k s d noiseCount tape ≠ finalOutput k s d noiseCount :=
  edgeSlot_ne_of_decode_none_inline_AddressMachineSpace k s d noiseCount tape _ rfl

theorem headerTape_ne_finalOutput (c : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount c ≠ finalOutput k s d noiseCount := by
  simp [headerTape, finalOutput]

theorem headerTape_ne_current (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ current k s d noiseCount j := by
  simp [headerTape, current]

theorem headerTape_ne_remaining (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ remaining k s d noiseCount j := by
  simp [headerTape, remaining]

theorem tupleOutput_headerTape (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple base k (headerTape k s d noiseCount c) =
      base (headerTape k s d noiseCount c) :=
  MachineSourceTuple.stageTapes_frame F tuple base k _
    (by simp [headerTape])
    (by simp [headerTape])
    (by intros; simp [headerTape])

theorem tupleOutput_source (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool) :
    MachineSourceTuple.stageTapes F tuple base k .source = base .source :=
  MachineSourceTuple.output_source F tuple base

theorem tupleOutput_rhs (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple base k (rhsField k s d noiseCount j) =
      encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++
        base (rhsField k s d noiseCount j) :=
  MachineSourceTuple.output_rhs F tuple base j

theorem tupleOutput_occurrence (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple base k
      (MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
        (.field (CanonicalBodyMachine.fieldIndex j 3))) = encodeWord (tuple j).val := by
  rw [addressSlots_occurrence]
  exact MachineSourceTuple.output_savedIndex_unary F tuple base hsaved j

end DFVSGames.Reduction.AddressMachineSpace
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
