import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.Foundations.PinskerLemmas
import OAI.Computability.UniqueGames.PCP.SourceNoiseParameterLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP

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
    Clause formula.variables := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot
abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.variables → Bool

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
  simp [accepts, (alice event.1).property, edgeProjection]
  rfl

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

def occurrenceCount (formula : Formula) (v : Fin formula.variables) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => occurrencesAt (clauseAt formula i) v + occurrenceCount formula v rest

theorem variable_eventsAt (formula : Formula) (v : Fin formula.variables)
    (i : Fin formula.clauses.length) :
    ((eventsAt formula i).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length =
      occurrencesAt (clauseAt formula i) v := by
  by_cases h₁ : (clauseAt formula i)[0].variableIndex = v <;>
    by_cases h₂ : (clauseAt formula i)[1].variableIndex = v <;>
    by_cases h₃ : (clauseAt formula i)[2].variableIndex = v <;>
    simp [eventsAt, nameAt, occurrencesAt, h₁, h₂, h₃]

theorem variable_enumerateEvents (formula : Formula) (v : Fin formula.variables)
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
    (regular : ∀ v : Fin formula.variables,
      occurrenceCount formula v (allIndices formula) = degree)
    (v : Fin formula.variables) :
    ((allEvents formula).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length = degree := by
  rw [allEvents, variable_enumerateEvents]
  exact regular v

end UniqueGamesTheorem.Foundations.PCP

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open Target PCP

/-- Executable tuple encoding of the eight clause answers. -/
def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

instance slotInhabited : Inhabited Slot := ⟨.first⟩

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev I (u : ℕ) := Fin u → Bool
abbrev J (u : ℕ) := Fin u → ClauseAnswer
abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.variables
abbrev SlotContext (u : ℕ) := Fin u → Slot

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]
@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.variables ^ u := by simp [VariableContext]
@[simp] theorem card_SlotContext (u : ℕ) :
    Fintype.card (SlotContext u) = 3 ^ u := by simp [SlotContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

/-- Satisfaction and consistency over all `3*u` occurrence slots. -/
def validJ (F : Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : Bool :=
  decide ((∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
    ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem validJ_eq_true_iff (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (j : J u) :
    validJ F c j = true ↔
      (∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
      ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
        answerAt (j t) s = answerAt (j t') s' := by
  simp [validJ]

theorem validJ_satisfies (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localSatisfies (clauseAt F (c t)) (j t) = true :=
  ((validJ_eq_true_iff F c j).mp hj).1 t

theorem validJ_consistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) (s : Slot)
    (t' : Fin u) (s' : Slot)
    (hname : nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s') :
    answerAt (j t) s = answerAt (j t') s' :=
  ((validJ_eq_true_iff F c j).mp hj).2 t t' s s' hname

theorem validJ_localConsistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localConsistent (clauseAt F (c t)) (j t) = true := by
  apply (localConsistent_eq_true_iff _ _).mpr
  intro s s' hs
  exact validJ_consistent F c j hj t s t s' hs

/-- First matching visible occurrence, with the third slot as an off-support
default. Its inputs contain no hidden incidence choice. -/
def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

theorem canonicalSlot_name {n : ℕ} (clause : Clause n) (v : Fin n)
    (hv : ∃ s, nameAt clause s = v) : nameAt clause (canonicalSlot clause v) = v := by
  by_cases hfirst : nameAt clause .first = v
  · simp [canonicalSlot, hfirst]
  by_cases hsecond : nameAt clause .second = v
  · simp [canonicalSlot, hfirst, hsecond]
  obtain ⟨s, hs⟩ := hv
  cases s with
  | first => exact False.elim (hfirst hs)
  | second => exact False.elim (hsecond hs)
  | third => simpa [canonicalSlot, hfirst, hsecond] using hs

def pi (F : Formula) {u : ℕ} (c : ClauseContext F u) (v : VariableContext F u)
    (j : J u) : I u :=
  fun t => answerAt (j t) (canonicalSlot (clauseAt F (c t)) (v t))

def sampledVariables (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : VariableContext F u :=
  fun t => nameAt (clauseAt F (c t)) (s t)

theorem sampledVariables_supported (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) :
    ∀ t, ∃ slot, nameAt (clauseAt F (c t)) slot = sampledVariables F c s t :=
  fun t => ⟨s t, rfl⟩

theorem sampled_eq_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (j : J u) (hj : validJ F c j = true)
    (t : Fin u) (s : Slot) (hs : nameAt (clauseAt F (c t)) s = v t) :
    answerAt (j t) s = pi F c v j t := by
  exact validJ_consistent F c j hj t s t
    (canonicalSlot (clauseAt F (c t)) (v t))
    (hs.trans (canonicalSlot_name _ _ ⟨s, hs⟩).symm)

/-- Two hidden choices with the same visible variable tuple give the same
selected answers for every valid label. -/
theorem sampled_answers_eq_of_visible_eq (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s s' : SlotContext u) (j : J u)
    (hj : validJ F c j = true)
    (hvisible : sampledVariables F c s = sampledVariables F c s') :
    (fun t => answerAt (j t) (s t)) = fun t => answerAt (j t) (s' t) := by
  funext t
  exact validJ_consistent F c j hj t (s t) t (s' t) (congrFun hvisible t)

def honestJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool) : J u :=
  fun t => honestAnswer (clauseAt F (c t)) assignment

def honestI (F : Formula) {u : ℕ} (v : VariableContext F u)
    (assignment : Fin F.variables → Bool) : I u :=
  fun t => assignment (v t)

theorem honestJ_valid (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    validJ F c (honestJ F c assignment) = true := by
  apply (validJ_eq_true_iff F c _).mpr
  constructor
  · intro t
    exact (honest_satisfies _ assignment).trans (hs _ (List.getElem_mem _))
  · intro t t' s s' hname
    simp only [honestJ, honest_answerAt]
    exact congrArg assignment hname

theorem pi_honest (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (assignment : Fin F.variables → Bool)
    (hsupport : ∀ t, ∃ s, nameAt (clauseAt F (c t)) s = v t) :
    pi F c v (honestJ F c assignment) = honestI F v assignment := by
  funext t
  exact (honest_answerAt _ assignment _).trans
    (congrArg assignment (canonicalSlot_name _ _ (hsupport t)))

theorem pi_honest_sampled (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (assignment : Fin F.variables → Bool) :
    pi F c (sampledVariables F c s) (honestJ F c assignment) =
      honestI F (sampledVariables F c s) assignment :=
  pi_honest F c _ assignment (sampledVariables_supported F c s)

def baseAccepts (F : Formula) (v : Fin F.variables) (c : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F c) j = true ∧
    localConsistent (clauseAt F c) j = true ∧
    answerAt j (canonicalSlot (clauseAt F c) v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.variables)
    (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v c i j = true ↔
      localSatisfies (clauseAt F c) j = true ∧
      localConsistent (clauseAt F c) j = true ∧
      answerAt j (canonicalSlot (clauseAt F c) v) = i := by
  simp [baseAccepts]

theorem projection_implies_coordinate_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (v : VariableContext F u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c v j = i) (t : Fin u) :
    baseAccepts F (v t) (c t) (i t) (j t) = true := by
  exact (baseAccepts_eq_true_iff F _ _ _ _).mpr
    ⟨validJ_satisfies F c j hj t, validJ_localConsistent F c j hj t, congrFun hpi t⟩

theorem baseAccepts_implies_sampled (F : Formula) (c : Fin F.clauses.length)
    (s : Slot) (i : Bool) (j : ClauseAnswer)
    (h : baseAccepts F (nameAt (clauseAt F c) s) c i j = true) :
    (localSatisfies (clauseAt F c) j && decide (answerAt j s = i)) = true := by
  obtain ⟨hsat, hcons, heq⟩ := (baseAccepts_eq_true_iff F _ _ _ _).mp h
  have hname := canonicalSlot_name (clauseAt F c) (nameAt (clauseAt F c) s) ⟨s, rfl⟩
  have hans := (localConsistent_eq_true_iff _ _).mp hcons s
    (canonicalSlot (clauseAt F c) (nameAt (clauseAt F c) s)) hname.symm
  simp [hsat, hans.trans heq]

/-- Every coordinate of the original repeated clause-slot verifier accepts
the decoded answers. Each answer tuple may depend on its whole private context. -/
theorem projection_implies_sampled_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c (sampledVariables F c s) j = i) :
    ∀ t, (localSatisfies (clauseAt F (c t)) (j t) &&
      decide (answerAt (j t) (s t) = i t)) = true := by
  intro t
  exact baseAccepts_implies_sampled F (c t) (s t) (i t) (j t)
    (projection_implies_coordinate_accepts F c _ i j hj hpi t)

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

/-- All local control data have sizes determined solely by the repetition
parameter. Global variable and clause indices are absent. -/
structure Signature (u : ℕ) where
  signs : Position u → Bool
  sameName : NameProfile u
  selected : SlotContext u
  deriving DecidableEq

def signatureEquiv (u : ℕ) :
    Signature u ≃ (Position u → Bool) × NameProfile u × SlotContext u where
  toFun σ := (σ.signs, σ.sameName, σ.selected)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv σ := by cases σ; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

instance signatureFintype (u : ℕ) : Fintype (Signature u) :=
  Fintype.ofEquiv ((Position u → Bool) × NameProfile u × SlotContext u)
    (signatureEquiv u).symm

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

/-- A finite control alphabet bound, not a claim about evaluation time. -/
theorem card_signature (u : ℕ) :
    Fintype.card (Signature u) =
      2 ^ (3 * u) * ((2 ^ (3 * u)) ^ (3 * u) * 3 ^ u) := by
  rw [Fintype.card_congr (signatureEquiv u)]
  simp [NameProfile, Nat.mul_comm]

def positiveAt {n : ℕ} (clause : Clause n) : Slot → Bool
  | .first => clause[0].positive
  | .second => clause[1].positive
  | .third => clause[2].positive

def occurrenceName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (p : Position u) : Fin F.variables :=
  nameAt (clauseAt F (c p.1)) p.2

/-- The equality matrix can be supplied by a separate field-comparison
procedure after an explicit reindexing of the `3*u` positions. -/
def contextNameProfile (F : Formula) {u : ℕ} (c : ClauseContext F u) : NameProfile u :=
  fun p q => decide (occurrenceName F c p = occurrenceName F c q)

def ofContext (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (selected : SlotContext u) : Signature u where
  signs p := positiveAt (clauseAt F (c p.1)) p.2
  sameName := contextNameProfile F c
  selected := selected

@[simp] theorem ofContext_signs (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p : Position u) :
    (ofContext F c s).signs p = positiveAt (clauseAt F (c p.1)) p.2 := rfl

@[simp] theorem ofContext_sameName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p q : Position u) :
    (ofContext F c s).sameName p q =
      decide (occurrenceName F c p = occurrenceName F c q) := rfl

@[simp] theorem ofContext_selected (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : (ofContext F c s).selected = s := rfl

/-- Local clause truth is computed from signs and the three answer bits. -/
def signatureSatisfies {u : ℕ} (σ : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (σ.signs (t, .first)) (j t).first ||
    literalValue (σ.signs (t, .second)) (j t).second) ||
    literalValue (σ.signs (t, .third)) (j t).third

def signatureValid {u : ℕ} (σ : Signature u) (j : J u) : Bool :=
  decide ((∀ t, signatureSatisfies σ j t = true) ∧
    ∀ t t' s s', σ.sameName (t, s) (t', s') = true →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem signatureSatisfies_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u) (t : Fin u) :
    signatureSatisfies (ofContext F c s) j t =
      localSatisfies (clauseAt F (c t)) (j t) := rfl

/-- Exact equality with the actual contextual validity predicate, for every
answer tuple, including repeated variables within or across clauses. -/
theorem signature_validJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureValid (ofContext F c s) j = validJ F c j := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hs := of_decide_eq_true h
    apply (validJ_eq_true_iff F c j).mpr
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).symm.trans (hs.1 t)
    · intro t t' a a' hname
      apply hs.2 t t' a a'
      exact decide_eq_true hname
  · intro h
    have hs := (validJ_eq_true_iff F c j).mp h
    apply decide_eq_true
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).trans (hs.1 t)
    · intro t t' a a' heq
      exact hs.2 t t' a a' (of_decide_eq_true heq)

/-- The first slot matching the visible selected name, computed using only
the equality matrix. The selected slot guarantees visible support. -/
def signatureCanonicalSlot {u : ℕ} (σ : Signature u) (t : Fin u) : Slot :=
  if σ.sameName (t, .first) (t, σ.selected t) then .first
  else if σ.sameName (t, .second) (t, σ.selected t) then .second else .third

def signatureProjection {u : ℕ} (σ : Signature u) (j : J u) : I u :=
  fun t => answerAt (j t) (signatureCanonicalSlot σ t)

theorem signatureCanonicalSlot_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (t : Fin u) :
    signatureCanonicalSlot (ofContext F c s) t =
      canonicalSlot (clauseAt F (c t)) (sampledVariables F c s t) := by
  by_cases hfirst : nameAt (clauseAt F (c t)) .first =
      nameAt (clauseAt F (c t)) (s t)
  · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
      occurrenceName, sampledVariables, hfirst]
  · by_cases hsecond : nameAt (clauseAt F (c t)) .second =
        nameAt (clauseAt F (c t)) (s t)
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]

/-- The actual canonical projection factors through the finite signature on
every label, without a validity hypothesis. -/
theorem signature_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureProjection (ofContext F c s) j = pi F c (sampledVariables F c s) j := by
  funext t
  simp only [signatureProjection, signatureCanonicalSlot_ofContext, pi]

/-- On valid labels, canonical projection also agrees with the actual
selected occurrence answers. -/
theorem signature_projection_selected (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u)
    (hj : signatureValid (ofContext F c s) j = true) :
    signatureProjection (ofContext F c s) j = fun t => answerAt (j t) (s t) := by
  rw [signature_pi]
  have hv : validJ F c j = true := by simpa only [signature_validJ] using hj
  funext t
  exact (sampled_eq_pi F c (sampledVariables F c s) j hv t (s t) rfl).symm

/-- The same finite signature gives the same validity decision even across
formulas having different global index types. -/
theorem validJ_eq_of_signature_eq (F G : Formula) {u : ℕ}
    (c : ClauseContext F u) (d : ClauseContext G u) (s s' : SlotContext u)
    (h : ofContext F c s = ofContext G d s') (j : J u) :
    validJ F c j = validJ G d j := by
  rw [← signature_validJ F c s, h, signature_validJ]

theorem pi_eq_of_signature_eq (F G : Formula) {u : ℕ}
    (c : ClauseContext F u) (d : ClauseContext G u) (s s' : SlotContext u)
    (h : ofContext F c s = ofContext G d s') (j : J u) :
    pi F c (sampledVariables F c s) j = pi G d (sampledVariables G d s') j := by
  rw [← signature_pi F c s, h, signature_pi]

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

end

end OAI
