import Mathlib
import OAI.Computability.MaxCut.Games.Target

namespace OAI

namespace MaxCutGames.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

theorem matchingSlots_le (a b : ClauseAnswer) : matchingSlots a b ≤ 3 := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

theorem matchingSlots_eq_three (a b : ClauseAnswer) : matchingSlots a b = 3 ↔ a = b := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

/-- A failed Bob clause forces one rejection among its three incidence events. -/
theorem local_rejection_bound {n : Nat} (clause : Clause n) (alice : ClauseAnswer)
    (bob : Fin n → Bool) :
    acceptedSlots clause alice (honestAnswer clause bob) + clauseFailure clause bob ≤ 3 := by
  have hle := matchingSlots_le alice (honestAnswer clause bob)
  by_cases hb : clause.eval bob = true
  · simp only [clauseFailure, hb, ↓reduceIte, Nat.add_zero]
    unfold acceptedSlots
    split <;> omega
  · have hfailure : clauseFailure clause bob = 1 := by simp [clauseFailure, hb]
    rw [hfailure]
    by_cases ha : localSatisfies clause alice = true
    · have hne : alice ≠ honestAnswer clause bob := by
        intro h
        subst alice
        exact hb ((honest_satisfies clause bob).symm.trans ha)
      have hlt : matchingSlots alice (honestAnswer clause bob) ≠ 3 := by
        intro h
        exact hne ((matchingSlots_eq_three _ _).mp h)
      simp only [acceptedSlots, ha, ↓reduceIte]
      omega
    · simp [acceptedSlots, ha]

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.«variables» := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot
abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.«variables» → Bool

/-- Explicit finite verifier. The occurrence and slot are randomness, never an
    additional argument supplied to Bob's strategy. -/
def accepts (formula : Formula) (alice : AliceStrategy formula) (bob : BobStrategy formula)
    (event : RandomEvent formula) : Bool :=
  localSatisfies (clauseAt formula event.1) (alice event.1) &&
    decide (answerAt (alice event.1) event.2 = bob (nameAt (clauseAt formula event.1) event.2))

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

theorem total_rejection_bound (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) (indices : List (Fin formula.clauses.length)) :
    acceptedCount formula alice bob indices + failureCount formula bob indices ≤
      3 * indices.length := by
  induction indices with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := local_rejection_bound (clauseAt formula i) (alice i) bob
    simp only [acceptedCount, failureCount, List.length_cons]
    omega

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

/-- Count form of Håstad Lemma 3.1: a fraction `a/b` of failed clauses gives
    a fraction at least `a/(3*b)` of failed verifier events. -/
theorem hastad_basic_verifier_soundness (formula : Formula) (a b : Nat)
    (sourceGap : ∀ bob : BobStrategy formula,
      a * formula.clauses.length ≤ b * failureCount formula bob (allIndices formula))
    (alice : AliceStrategy formula) (bob : BobStrategy formula) :
    b * acceptedCount formula alice bob (allIndices formula) + a * formula.clauses.length ≤
      b * (3 * formula.clauses.length) := by
  have ht := Nat.mul_le_mul_left b (total_rejection_bound formula alice bob (allIndices formula))
  have hg := sourceGap bob
  simp only [allIndices, List.length_finRange, Nat.mul_add] at *
  omega

theorem honest_accepts (formula : Formula) (assignment : BobStrategy formula)
    (satisfies : ∀ clause ∈ formula.clauses, clause.eval assignment = true)
    (event : RandomEvent formula) :
    accepts formula (fun i => honestAnswer (clauseAt formula i) assignment) assignment event = true := by
  have hc : (clauseAt formula event.1).eval assignment = true :=
    satisfies _ (List.getElem_mem _)
  simp [accepts, honest_satisfies, honest_answerAt, hc]

/-- Pointwise perfect completeness, including the exact input syntax. -/
theorem verifier_completeness (formula : Formula) (sat : formula.Satisfiable) :
    ∃ (alice : AliceStrategy formula) (bob : BobStrategy formula),
      ∀ event : RandomEvent formula, accepts formula alice bob event = true := by
  rcases sat with ⟨assignment, hs⟩
  exact ⟨fun i => honestAnswer (clauseAt formula i) assignment, assignment,
    honest_accepts formula assignment hs⟩

/-- The valid left labels and projection maps give the concrete Label Cover
    presentation. Their alphabet depends on the clause, with at most 8 bit triples. -/
abbrev LeftLabel (formula : Formula) (i : Fin formula.clauses.length) :=
  { answer : ClauseAnswer // localSatisfies (clauseAt formula i) answer = true }

def edgeProjection (formula : Formula) (event : RandomEvent formula)
    (label : LeftLabel formula event.1) : Bool := answerAt label.val event.2

theorem verifier_eq_projection (formula : Formula)
    (alice : ∀ i, LeftLabel formula i) (bob : BobStrategy formula) (event : RandomEvent formula) :
    accepts formula (fun i => (alice i).val) bob event =
      decide (edgeProjection formula event (alice event.1) =
        bob (nameAt (clauseAt formula event.1) event.2)) := by
  simp [accepts, (alice event.1).property, edgeProjection] ; rfl

/-- A materialized list of all three slot events at an occurrence. -/
def eventsAt (formula : Formula) (i : Fin formula.clauses.length) : List (RandomEvent formula) :=
  [(i, .first), (i, .second), (i, .third)]

def enumerateEvents (formula : Formula) : List (Fin formula.clauses.length) →
    List (RandomEvent formula)
  | [] => []
  | i :: rest => eventsAt formula i ++ enumerateEvents formula rest

theorem length_enumerateEvents (formula : Formula) (indices : List (Fin formula.clauses.length)) :
    (enumerateEvents formula indices).length = 3 * indices.length := by
  induction indices with
  | nil => simp [enumerateEvents]
  | cons i rest ih =>
    simp only [enumerateEvents, eventsAt, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem accepted_eventsAt (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) (i : Fin formula.clauses.length) :
    ((eventsAt formula i).filter (accepts formula alice bob)).length =
      acceptedSlots (clauseAt formula i) (alice i) (honestAnswer (clauseAt formula i) bob) := by
  by_cases hs : localSatisfies (clauseAt formula i) (alice i) = true
  · by_cases h₁ : (alice i).first = bob (clauseAt formula i)[0].variableIndex <;>
      by_cases h₂ : (alice i).second = bob (clauseAt formula i)[1].variableIndex <;>
      by_cases h₃ : (alice i).third = bob (clauseAt formula i)[2].variableIndex <;>
      simp [eventsAt, accepts, acceptedSlots, matchingSlots, honestAnswer,
        answerAt, nameAt, hs, h₁, h₂, h₃]
  · simp [eventsAt, accepts, acceptedSlots, hs]

/-- The rejection-count proof counts exactly the explicit verifier's accepted
    random events; it is not a separate abstract score. -/
theorem accepted_enumerateEvents (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) (indices : List (Fin formula.clauses.length)) :
    ((enumerateEvents formula indices).filter (accepts formula alice bob)).length =
      acceptedCount formula alice bob indices := by
  induction indices with
  | nil => simp [enumerateEvents, acceptedCount]
  | cons i rest ih =>
    simp only [enumerateEvents, List.filter_append, List.length_append,
      accepted_eventsAt, ih, acceptedCount]

def allEvents (formula : Formula) : List (RandomEvent formula) :=
  enumerateEvents formula (allIndices formula)

theorem length_allEvents (formula : Formula) :
    (allEvents formula).length = 3 * formula.clauses.length := by
  simp [allEvents, length_enumerateEvents, allIndices]

theorem allEvents_nonempty (formula : Formula) (hne : formula.clauses ≠ []) :
    allEvents formula ≠ [] := by
  intro he
  have hl := length_allEvents formula
  rw [he] at hl
  have hpos : 0 < formula.clauses.length := List.length_pos_iff.mpr hne
  simp only [List.length_nil] at hl
  omega

/-- Soundness stated solely in terms of filtering the generated event list.
    For `b>0` and a nonempty input, division by `b*|allEvents|` gives the
    usual normalized acceptance probability. -/
theorem verifier_event_soundness (formula : Formula) (a b : Nat)
    (sourceGap : ∀ bob : BobStrategy formula,
      a * formula.clauses.length ≤ b * failureCount formula bob (allIndices formula))
    (alice : AliceStrategy formula) (bob : BobStrategy formula) :
    b * ((allEvents formula).filter (accepts formula alice bob)).length +
      a * formula.clauses.length ≤ b * (allEvents formula).length := by
  rw [length_allEvents]
  simp only [allEvents, accepted_enumerateEvents]
  exact hastad_basic_verifier_soundness formula a b sourceGap alice bob

/-- Count the syntactic occurrences of one variable in each three-slot clause. -/
def occurrencesAt {n : Nat} (clause : Clause n) (v : Fin n) : Nat :=
  (if clause[0].variableIndex = v then 1 else 0) +
  (if clause[1].variableIndex = v then 1 else 0) +
  (if clause[2].variableIndex = v then 1 else 0)

def occurrenceCount (formula : Formula) (v : Fin formula.«variables») :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => occurrencesAt (clauseAt formula i) v + occurrenceCount formula v rest

theorem variable_eventsAt (formula : Formula) (v : Fin formula.«variables»)
    (i : Fin formula.clauses.length) :
    ((eventsAt formula i).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length =
      occurrencesAt (clauseAt formula i) v := by
  by_cases h₁ : (clauseAt formula i)[0].variableIndex = v <;>
    by_cases h₂ : (clauseAt formula i)[1].variableIndex = v <;>
    by_cases h₃ : (clauseAt formula i)[2].variableIndex = v <;>
    simp [eventsAt, nameAt, occurrencesAt, h₁, h₂, h₃]

theorem variable_enumerateEvents (formula : Formula) (v : Fin formula.«variables»)
    (indices : List (Fin formula.clauses.length)) :
    ((enumerateEvents formula indices).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length =
      occurrenceCount formula v indices := by
  induction indices with
  | nil => simp [enumerateEvents, occurrenceCount]
  | cons i rest ih =>
    simp only [enumerateEvents, List.filter_append, List.length_append,
      variable_eventsAt, ih, occurrenceCount]

theorem regular_bob_marginal (formula : Formula) (degree : Nat)
    (regular : ∀ v : Fin formula.«variables»,
      occurrenceCount formula v (allIndices formula) = degree)
    (v : Fin formula.«variables») :
    ((allEvents formula).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length = degree := by
  rw [allEvents, variable_enumerateEvents]
  exact regular v

end MaxCutGames.Foundations.PCP

end OAI
