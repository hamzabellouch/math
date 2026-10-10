import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Computation.Machine

namespace OAI

namespace BinPackingGames.Foundations.PCP

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

theorem verifier_completeness (formula : Formula) (sat : formula.Satisfiable) :
    ∃ (alice : AliceStrategy formula) (bob : BobStrategy formula),
      ∀ event : RandomEvent formula, accepts formula alice bob event = true := by
  rcases sat with ⟨assignment, hs⟩
  exact ⟨fun i => honestAnswer (clauseAt formula i) assignment, assignment,
    honest_accepts formula assignment hs⟩

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

theorem verifier_event_soundness (formula : Formula) (a b : Nat)
    (sourceGap : ∀ bob : BobStrategy formula,
      a * formula.clauses.length ≤ b * failureCount formula bob (allIndices formula))
    (alice : AliceStrategy formula) (bob : BobStrategy formula) :
    b * ((allEvents formula).filter (accepts formula alice bob)).length +
      a * formula.clauses.length ≤ b * (allEvents formula).length := by
  rw [length_allEvents]
  simp only [allEvents, accepted_enumerateEvents]
  exact hastad_basic_verifier_soundness formula a b sourceGap alice bob

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

end BinPackingGames.Foundations.PCP

namespace BinPackingGames.Foundations.PCP.NameCompaction

open BinPackingGames.Foundations.Target

def clauseNames {n : Nat} (c : Clause n) : List (Fin n) :=
  [(c)[0].variableIndex, (c)[1].variableIndex, (c)[2].variableIndex]

def sourceNames (F : Formula) : List (Fin F.variables) :=
  F.clauses.flatMap clauseNames

def activeNames (F : Formula) : List (Fin F.variables) :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) (c : Clause F.variables)
    (hc : c ∈ F.clauses) (i : Fin 3) :
    (c)[i].variableIndex ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Fin F.variables)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Fin F.variables :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal F.variables)
    (hl : l.variableIndex ∈ activeNames F) : Literal (activeNames F).length :=
  ⟨compactIndex F l.variableIndex hl, l.positive⟩

def compactClause (F : Formula) (c : Clause F.variables)
    (hc : c ∈ F.clauses) : Clause (activeNames F).length :=
  #v[compactLiteral F (c)[0] (literal_mem_active F c hc 0),
    compactLiteral F (c)[1] (literal_mem_active F c hc 1),
    compactLiteral F (c)[2] (literal_mem_active F c hc 2)]

def compactClauses (F : Formula) : List (Clause (activeNames F).length) :=
  F.clauses.attach.map (fun c => compactClause F c.val c.property)

def compact (F : Formula) : Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Fin F.variables → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Fin F.variables) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Fin F.variables)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

@[simp] theorem eval_compact_restrict (F : Formula) (c : Clause F.variables)
    (hc : c ∈ F.clauses) (A : Fin F.variables → Bool) :
    (compactClause F c hc).eval (restrictAssignment F A) = c.eval A := by
  simp [compactClause, compactLiteral, Clause.eval, Literal.eval,
    restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) (c : Clause F.variables)
    (hc : c ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F c hc).eval B = c.eval (extendAssignment F B) := by
  have h₀ : (c)[0].variableIndex ∈ activeNames F := literal_mem_active F c hc 0
  have h₁ : (c)[1].variableIndex ∈ activeNames F := literal_mem_active F c hc 1
  have h₂ : (c)[2].variableIndex ∈ activeNames F := literal_mem_active F c hc 2
  simp [compactClause, compactLiteral, Clause.eval, Literal.eval, extendAssignment,
    h₀, h₁, h₂]
  rfl

theorem map_attach_val {α β : Type} (xs : List α) (f : α → β) :
    xs.attach.map (fun x => f x.val) = xs.map f := by
  exact List.attach_map_val

def evaluationList (F : Formula) (A : Fin F.variables → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

def satisfiedCount (F : Formula) (A : Fin F.variables → Bool) : Nat :=
  (evaluationList F A).count true

def failedCount (F : Formula) (A : Fin F.variables → Bool) : Nat :=
  (evaluationList F A).count false

theorem evaluationList_restrict (F : Formula) (A : Fin F.variables → Bool) :
    evaluationList (compact F) (restrictAssignment F A) = evaluationList F A := by
  simp only [evaluationList, compact, compactClauses, List.map_map]
  simpa only [Function.comp_def, eval_compact_restrict] using
    map_attach_val F.clauses (fun c => c.eval A)

theorem evaluationList_extend (F : Formula) (B : Fin (compact F).variables → Bool) :
    evaluationList (compact F) B = evaluationList F (extendAssignment F B) := by
  simp only [evaluationList, compact, compactClauses, List.map_map]
  change F.clauses.attach.map (fun c => (compactClause F c.val c.property).eval B) = _
  calc
    _ = F.clauses.attach.map (fun c => c.val.eval (extendAssignment F B)) := by
      apply List.map_congr_left
      intro c _
      exact eval_compact_extend F c.val c.property B
    _ = _ := map_attach_val F.clauses (fun c => c.eval (extendAssignment F B))

theorem satisfiedCount_restrict (F : Formula) (A : Fin F.variables → Bool) :
    satisfiedCount (compact F) (restrictAssignment F A) = satisfiedCount F A := by
  simp only [satisfiedCount, evaluationList_restrict]

theorem failedCount_restrict (F : Formula) (A : Fin F.variables → Bool) :
    failedCount (compact F) (restrictAssignment F A) = failedCount F A := by
  simp only [failedCount, evaluationList_restrict]

theorem satisfiedCount_extend (F : Formula) (B : Fin (compact F).variables → Bool) :
    satisfiedCount (compact F) B = satisfiedCount F (extendAssignment F B) := by
  simp only [satisfiedCount, evaluationList_extend]

theorem failedCount_extend (F : Formula) (B : Fin (compact F).variables → Bool) :
    failedCount (compact F) B = failedCount F (extendAssignment F B) := by
  simp only [failedCount, evaluationList_extend]

theorem clauseNames_flat_length {n : Nat} (cs : List (Clause n)) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem compact_clause_count (F : Formula) :
    (compact F).clauses.length = F.clauses.length := by
  simp [compact, compactClauses]

theorem length_eraseDups_le {α : Type} [BEq α] (xs : List α) :
    xs.eraseDups.length ≤ xs.length := by
  match xs with
  | [] => simp
  | a :: rest =>
    rw [List.eraseDups_cons]
    have filtered := List.length_filter_le (fun b => !(b == a)) rest
    have ih := length_eraseDups_le (rest.filter (fun b => !(b == a)))
    simp only [List.length_cons]
    omega
termination_by xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem compact_active_bound (F : Formula) :
    (compact F).variables ≤ 3 * F.clauses.length := by
  have h := length_eraseDups_le (sourceNames F)
  simpa only [sourceNames, clauseNames_flat_length, compact, activeNames] using h

theorem compact_completeness (F : Formula) (hs : F.Satisfiable) :
    (compact F).Satisfiable := by
  rcases hs with ⟨A, hA⟩
  refine ⟨restrictAssignment F A, ?_⟩
  intro d hd
  change d ∈ F.clauses.attach.map (fun c => compactClause F c.val c.property) at hd
  rcases List.mem_map.mp hd with ⟨c, _, rfl⟩
  exact (eval_compact_restrict F c.val c.property A).trans (hA c.val c.property)

theorem compact_reflects (F : Formula) (hs : (compact F).Satisfiable) :
    F.Satisfiable := by
  rcases hs with ⟨B, hB⟩
  refine ⟨extendAssignment F B, ?_⟩
  intro c hc
  have hm : compactClause F c hc ∈ (compact F).clauses := by
    change _ ∈ F.clauses.attach.map (fun d => compactClause F d.val d.property)
    exact List.mem_map.mpr ⟨⟨c, hc⟩, by simp, rfl⟩
  rw [← eval_compact_extend F c hc B]
  exact hB _ hm

theorem compact_satisfiable_iff (F : Formula) :
    (compact F).Satisfiable ↔ F.Satisfiable :=
  ⟨compact_reflects F, compact_completeness F⟩

theorem compact_preserves_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * failedCount F A)
    (B : Fin (compact F).variables → Bool) :
    a * (compact F).clauses.length ≤ b * failedCount (compact F) B := by
  rw [compact_clause_count, failedCount_extend]
  exact gap (extendAssignment F B)

theorem compact_encoding_bound (F : Formula) :
    (Complexity.formulaBits (compact F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have enc := Complexity.formulaBits_length_le (compact F)
  rw [compact_clause_count] at enc
  have active := compact_active_bound F
  have h₁ := Nat.add_le_add_right active (F.clauses.length + 2)
  have h₂ := Nat.mul_le_mul_left F.clauses.length
    (Nat.mul_le_mul_left 3 (Nat.add_le_add_right active 2))
  have total := Nat.add_le_add h₁ h₂
  have polynomial : 3 * F.clauses.length + (F.clauses.length + 2) +
      F.clauses.length * (3 * (3 * F.clauses.length + 2)) =
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [polynomial] at total
  omega

theorem failureCount_evaluations (F : Formula) (A : Fin F.variables → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

theorem evaluations_allIndices (F : Formula) (A : Fin F.variables → Bool) :
    ((allIndices F).map (fun i => (clauseAt F i).eval A)) = evaluationList F A := by
  calc
    _ = (List.ofFn (fun i : Fin F.clauses.length => F.clauses[i.val])).map
        (fun c => c.eval A) := by
      simp only [allIndices, List.finRange, clauseAt, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.ofFn_getElem]; rfl

theorem verifier_failureCount (F : Formula) (A : Fin F.variables → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

theorem compact_verifier_soundness (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * failedCount F A)
    (alice : AliceStrategy (compact F)) (bob : BobStrategy (compact F)) :
    b * ((allEvents (compact F)).filter (accepts (compact F) alice bob)).length +
        a * F.clauses.length ≤ b * (3 * F.clauses.length) := by
  have sourceGap : ∀ A : BobStrategy (compact F),
      a * (compact F).clauses.length ≤
        b * failureCount (compact F) A (allIndices (compact F)) := by
    intro A
    rw [verifier_failureCount]
    exact compact_preserves_gap F a b gap A
  have h := verifier_event_soundness (compact F) a b sourceGap alice bob
  simpa only [length_allEvents, compact_clause_count] using h

end BinPackingGames.Foundations.PCP.NameCompaction

namespace BinPackingGames.Foundations.PCP.VerifierToCNF

open Target

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

abbrev Pattern (q : Nat) := Fin q → Bool

def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.variables + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.variables) : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.variables (finProdFinEquiv (finProdFinEquiv (e, p), j))

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.variables + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.variables) :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.variables :=
  ⟨V.query e i, !(patternAt q p i)⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.variables → Bool :=
  fun v => B (oldIndex V v)

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (v : Fin V.variables) :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem convert_nonempty {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (eventsPositive : 0 < V.events) : (convert V hq).clauses ≠ [] := by
  have p : 0 < (convert V hq).clauses.length := by
    rw [convert_clause_count]
    exact Nat.mul_pos eventsPositive (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega))
  intro empty
  simp only [empty, List.length_nil] at p
  omega

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

theorem convert_gap {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (a b : Nat)
    (gap : ∀ A, a * V.events ≤ b * rejectedEventCount V A)
    (B : Fin (outputVariables V) → Bool) :
    a * (convert V hq).clauses.length ≤
      (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by
  have eventGap := gap (restrictAssignment V B)
  have countBound := Nat.mul_le_mul_left b (convert_count_bridge V hq B)
  rw [convert_clause_count]
  calc
    a * (V.events * (2 ^ q * (q - 2))) = (a * V.events) * (2 ^ q * (q - 2)) := by
      rw [Nat.mul_assoc]
    _ ≤ (b * NameCompaction.failedCount (convert V hq) B) * (2 ^ q * (q - 2)) :=
      Nat.mul_le_mul_right _ (eventGap.trans countBound)
    _ = (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by ac_rfl

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

def padLiteral {n : Nat} (l : Literal n) : Literal (n + 1) :=
  ⟨Fin.castAdd 1 l.variableIndex, l.positive⟩

def padClause {n : Nat} (c : Clause n) : Clause (n + 1) :=
  #v[padLiteral (c)[0], padLiteral (c)[1], padLiteral (c)[2]]

def padTautology (n : Nat) : Clause (n + 1) :=
  let v := Fin.natAdd n (0 : Fin 1)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def padInput (F : Formula) : Formula where
  «variables» := F.variables + 1
  clauses := F.clauses.map padClause ++ [padTautology F.variables]

theorem padClause_eval {n : Nat} (c : Clause n) (B : Fin (n + 1) → Bool) :
    (padClause c).eval B = c.eval (fun v => B (Fin.castAdd 1 v)) := rfl

theorem padTautology_satisfied (n : Nat) (B : Fin (n + 1) → Bool) :
    (padTautology n).eval B = true := by
  simp [padTautology, Clause.eval, Literal.eval]

theorem padInput_satisfiable_iff (F : Formula) : (padInput F).Satisfiable ↔ F.Satisfiable := by
  change (∃ B : Fin (F.variables + 1) → Bool,
    ∀ c ∈ F.clauses.map padClause ++ [padTautology F.variables], c.eval B = true) ↔ _
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨fun v => B (Fin.castAdd 1 v), fun c hc => ?_⟩
    have hmem : padClause c ∈ (padInput F).clauses := by
      apply List.mem_append.mpr
      exact Or.inl (List.mem_map.mpr ⟨c, hc, rfl⟩)
    exact (padClause_eval c B).symm.trans (hB _ hmem)
  · rintro ⟨A, hA⟩
    let B : Fin (F.variables + 1) → Bool := Fin.addCases A (fun _ => false)
    refine ⟨B, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with original | padding
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp original
      have h := hA d hd
      simpa only [padClause_eval, B, Fin.addCases_left] using h
    · have hc : c = padTautology F.variables := by simpa using padding
      subst c
      exact padTautology_satisfied F.variables B

@[simp] theorem padInput_clause_count (F : Formula) :
    (padInput F).clauses.length = F.clauses.length + 1 := by simp [padInput]

theorem padInput_nonempty (F : Formula) : (padInput F).clauses ≠ [] := by
  intro empty
  have size := padInput_clause_count F
  rw [empty, List.length_nil] at size
  omega

def prepareInput (F : Formula) : Formula := NameCompaction.compact (padInput F)

theorem prepareInput_satisfiable_iff (F : Formula) :
    (prepareInput F).Satisfiable ↔ F.Satisfiable :=
  (NameCompaction.compact_satisfiable_iff (padInput F)).trans (padInput_satisfiable_iff F)

theorem prepareInput_clause_count (F : Formula) :
    (prepareInput F).clauses.length = F.clauses.length + 1 := by
  simp only [prepareInput, NameCompaction.compact_clause_count, padInput_clause_count]

theorem prepareInput_nonempty (F : Formula) : (prepareInput F).clauses ≠ [] := by
  intro empty
  have h := prepareInput_clause_count F
  rw [empty, List.length_nil] at h
  omega

theorem prepareInput_variable_bound (F : Formula) :
    (prepareInput F).variables ≤ 3 * (F.clauses.length + 1) := by
  simpa only [prepareInput, padInput_clause_count] using NameCompaction.compact_active_bound (padInput F)

end BinPackingGames.Foundations.PCP.VerifierToCNF

namespace BinPackingCompleteness.BinaryFormula

open BinPackingGames.Foundations

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

def clauseNames (c : Clause) : List Nat :=
  [(c)[0].name, (c)[1].name, (c)[2].name]

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (i : Fin 3) : (c)[i].name ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Nat :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

def compactClause (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) : Target.Clause (activeNames F).length :=
  #v[compactLiteral F (c)[0] (literal_mem_active F c hc 0),
    compactLiteral F (c)[1] (literal_mem_active F c hc 1),
    compactLiteral F (c)[2] (literal_mem_active F c hc 2)]

def compactClauses (F : Formula) : List (Target.Clause (activeNames F).length) :=
  F.clauses.attach.map (fun c => compactClause F c.val c.property)

def dense (F : Formula) : Target.Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Nat) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

theorem compactIndex_injective (F : Formula) (u v : Nat)
    (hu : u ∈ activeNames F) (hv : v ∈ activeNames F)
    (h : compactIndex F u hu = compactIndex F v hv) : u = v := by
  have decoded := congrArg (decodeName F) h
  simpa only [decode_compactIndex] using decoded

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

@[simp] theorem eval_compact_restrict (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (A : Nat → Bool) :
    (compactClause F c hc).eval (restrictAssignment F A) = c.eval A := by
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F c hc).eval B = c.eval (extendAssignment F B) := by
  have h₀ : (c)[0].name ∈ activeNames F := literal_mem_active F c hc 0
  have h₁ : (c)[1].name ∈ activeNames F := literal_mem_active F c hc 1
  have h₂ : (c)[2].name ∈ activeNames F := literal_mem_active F c hc 2
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, extendAssignment, h₀, h₁, h₂]
  rfl

def evaluationList (F : Formula) (A : Nat → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

theorem evaluationList_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.evaluationList (dense F) (restrictAssignment F A) =
      evaluationList F A := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  simpa only [Function.comp_def, eval_compact_restrict] using
    PCP.NameCompaction.map_attach_val F.clauses (fun c => c.eval A)

theorem evaluationList_extend (F : Formula) (B : Fin (dense F).variables → Bool) :
    PCP.NameCompaction.evaluationList (dense F) B =
      evaluationList F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  change F.clauses.attach.map (fun c => (compactClause F c.val c.property).eval B) = _
  calc
    _ = F.clauses.attach.map (fun c => c.val.eval (extendAssignment F B)) := by
      apply List.map_congr_left
      intro c _
      exact eval_compact_extend F c.val c.property B
    _ = _ := PCP.NameCompaction.map_attach_val F.clauses
      (fun c => c.eval (extendAssignment F B))

def failedCount (F : Formula) (A : Nat → Bool) : Nat :=
  (evaluationList F A).count false

theorem failedCount_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.failedCount (dense F) (restrictAssignment F A) = failedCount F A := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_restrict]

theorem failedCount_extend (F : Formula) (B : Fin (dense F).variables → Bool) :
    PCP.NameCompaction.failedCount (dense F) B = failedCount F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_extend]

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem dense_clause_count (F : Formula) :
    (dense F).clauses.length = F.clauses.length := by
  simp [dense, compactClauses]

theorem dense_variable_bound (F : Formula) :
    (dense F).variables ≤ 3 * F.clauses.length := by
  have h := PCP.NameCompaction.length_eraseDups_le (sourceNames F)
  simpa only [sourceNames, clauseNames_flat_length, dense, activeNames] using h

theorem dense_completeness (F : Formula) (hs : F.Satisfiable) :
    (dense F).Satisfiable := by
  rcases hs with ⟨A, hA⟩
  refine ⟨restrictAssignment F A, ?_⟩
  intro d hd
  change d ∈ F.clauses.attach.map (fun c => compactClause F c.val c.property) at hd
  rcases List.mem_map.mp hd with ⟨c, _, rfl⟩
  exact (eval_compact_restrict F c.val c.property A).trans (hA c.val c.property)

theorem dense_reflects (F : Formula) (hs : (dense F).Satisfiable) : F.Satisfiable := by
  rcases hs with ⟨B, hB⟩
  refine ⟨extendAssignment F B, ?_⟩
  intro c hc
  have hm : compactClause F c hc ∈ (dense F).clauses := by
    change _ ∈ F.clauses.attach.map (fun d => compactClause F d.val d.property)
    exact List.mem_map.mpr ⟨⟨c, hc⟩, by simp, rfl⟩
  rw [← eval_compact_extend F c hc B]
  exact hB _ hm

theorem dense_satisfiable_iff (F : Formula) :
    (dense F).Satisfiable ↔ F.Satisfiable :=
  ⟨dense_reflects F, dense_completeness F⟩

theorem dense_preserves_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * failedCount F A)
    (B : Fin (dense F).variables → Bool) :
    a * (dense F).clauses.length ≤ b * PCP.NameCompaction.failedCount (dense F) B := by
  rw [dense_clause_count, failedCount_extend]
  exact gap (extendAssignment F B)

theorem dense_encoding_bound (F : Formula) :
    (Complexity.formulaBits (dense F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have enc := Complexity.formulaBits_length_le (dense F)
  rw [dense_clause_count] at enc
  have active := dense_variable_bound F
  have h₁ := Nat.add_le_add_right active (F.clauses.length + 2)
  have h₂ := Nat.mul_le_mul_left F.clauses.length
    (Nat.mul_le_mul_left 3 (Nat.add_le_add_right active 2))
  have total := Nat.add_le_add h₁ h₂
  have polynomial : 3 * F.clauses.length + (F.clauses.length + 2) +
      F.clauses.length * (3 * (3 * F.clauses.length + 2)) =
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
    ring
  rw [polynomial] at total
  omega

end BinPackingCompleteness.BinaryFormula

end OAI
