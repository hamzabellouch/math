import OAI.Computability.UniqueGames.PCP.AlphabetGraphLemmas
import OAI.Computability.UniqueGames.PCP.GraphTables

namespace OAI

section

/-! Executable six-query generation on fixed full Boolean cubes. The event
type is exactly `AlphabetGraph.LocalEvent`, including all five full tapes.
Only the returned joint-table addresses are masked outside the input relation;
no legal-pair enumeration or change of sample multiplicities occurs. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries

open UniqueGamesTheorem.Foundations.Hastad

abbrev RawQuery (q : Nat) :=
  (Bool × Cube (Fin q)) ⊕ Cube (Fin q × Fin q)

abbrev LocalEvent (q : Nat) := AlphabetGraph.LocalEvent (Fin q)

/-- Canonical full-cube proof address: every illegal coordinate is false. -/
def mask {q : Nat} (P : Fin q → Fin q → Bool) (f : Cube (Fin q × Fin q)) :
    Cube (Fin q × Fin q) := fun p => if P p.1 p.2 then f p else false

def xorTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a ^^ g a

def andTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a && g a

/-- The coordinate value of the paired input codeword before masking. -/
def inputPairTape {q : Nat} (k : Bool × Cube (Fin q)) : Cube (Fin q × Fin q) :=
  fun p => if k.1 then k.2 p.2 else k.2 p.1

/-- Actual six queries, computed directly from fixed full tapes and P.
Padding slots repeat precisely the addresses used by `eventQueries`. -/
def query {q : Nat} (P : Fin q → Fin q → Bool) (event : LocalEvent q)
    (slot : Fin 6) : RawQuery q :=
  match event with
  | (kind, k, f, g, r₀, r₁, r₂) =>
    if kind = 0 then
      if slot = 0 then .inr (mask P f) else
      if slot = 1 then .inr (mask P g) else .inr (mask P (xorTape f g))
    else if kind = 1 then
      if slot = 0 then .inr (mask P r₀) else
      if slot = 1 then .inr (mask P (xorTape r₀ (andTape f g))) else
      if slot = 2 then .inr (mask P r₁) else
      if slot = 3 then .inr (mask P (xorTape r₁ f)) else
      if slot = 4 then .inr (mask P r₂) else .inr (mask P (xorTape r₂ g))
    else if kind = 2 then
      if slot = 0 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (fun _ => true)))
    else
      if slot = 0 then .inl k else
      if slot = 1 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (inputPairTape k)))

/-- Attach the actual endpoints and edge identifier to a local raw address. -/
def globalize {q : Nat} {V E : Type*} (tail head : V) (edge : E) :
    RawQuery q → AlphabetGraph.Address V E (Fin q)
  | .inl (side, tape) => .inl ((if side then head else tail), tape)
  | .inr tape => .inr (edge, tape)

@[simp] theorem mask_idempotent {q : Nat} (P : Fin q → Fin q → Bool)
    (f : Cube (Fin q × Fin q)) : mask P (mask P f) = mask P f := by
  funext p
  cases hp : P p.1 p.2 <;> simp [mask, hp]

theorem mask_of_empty {q : Nat} (P : Fin q → Fin q → Bool)
    (empty : ∀ a b, P a b = false) (f : Cube (Fin q × Fin q)) :
    mask P f = fun _ => false := by
  funext p
  simp [mask, empty]

/-- Every joint-table query is already a canonical masked full tape. -/
theorem query_is_masked {q : Nat} (P : Fin q → Fin q → Bool)
    (event : LocalEvent q) (slot : Fin 6) :
    match query P event slot with
    | .inl _ => True
    | .inr tape => mask P tape = tape := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, hk₀, hk₁, hk₂, ite_true, ite_false] <;>
    split_ifs <;> simp

/-- Proof-only comparison map: extend the original legal-coordinate addresses.
The executable `query` function above never calls this map. -/
def extendQuery {q : Nat} (P : Fin q → Fin q → Bool) :
    AlphabetReduction.InputCoordinate (Fin q) ⊕ Cube (AlphabetReduction.LegalPair P) →
      RawQuery q
  | .inl k => .inl k
  | .inr tape => .inr (UniformRestriction.extend (fun p : Fin q × Fin q => P p.1 p.2 = true) tape)

/-- Pointwise equality with the existing tester after restricting all five
full input tapes and canonically extending the resulting query. The statement
does not require any legal pair to exist. -/
theorem query_eq_extend_eventQueries {q : Nat} (P : Fin q → Fin q → Bool)
    (kind : Fin 4) (k : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) (slot : Fin 6) :
    query P (kind, k, f, g, r₀, r₁, r₂) slot =
      extendQuery P (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding P) kind k
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) f)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) g)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₀)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₁)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₂) slot) := by
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, AssignmentTester.eventQueries, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> simp_all only [extendQuery]
  all_goals rfl

theorem globalize_extendQuery {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E)
    (x : AlphabetReduction.InputCoordinate (Fin q) ⊕
      Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    globalize (G.tail e) (G.head e) e (extendQuery (G.accepts e) x) =
      AlphabetGraph.globalizeQuery G e x := by
  cases x with
  | inl k => cases k; rfl
  | inr tape => rfl

/-- The executable raw queries are exactly the actual verifier queries after
attaching the endpoints and edge tag. This includes self-loops, duplicate
queries, empty legal relations, and every original five-tape event. -/
theorem globalize_query {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E) (event : LocalEvent q) (slot : Fin 6) :
    globalize (G.tail e) (G.head e) e (query (G.accepts e) event slot) =
      (AlphabetGraph.verifier G).query (e, event) slot := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rw [query_eq_extend_eventQueries]
  exact globalize_extendQuery G e _

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries

end

section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

/-- Exact local address comparison. A loop identifies the two endpoint tables;
the joint edge table is always disjoint from every endpoint table. -/
def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

/-- Search the fixed six positions for the least occurrence of an address. -/
def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

theorem canonicalSlot_profile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries (canonicalSlot selfLoop queries i) i = true := by
  unfold canonicalSlot
  exact Fin.find_spec (p := fun j => eqProfile selfLoop queries j i = true)
    ⟨i, eqProfile_refl _ _ _⟩

theorem canonicalSlot_le (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) (h : eqProfile selfLoop queries j i = true) :
    canonicalSlot selfLoop queries i ≤ j :=
  Fin.find_le_of_pos ⟨i, eqProfile_refl _ _ _⟩ h

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

/-- A complete 64-by-64 Boolean relation in the shared row-major table format. -/
def relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable :=
  GraphTables.relationOf fun a b =>
    predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
      slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)

@[simp] theorem relationAt_relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot orientation) a b =
      predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
        slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  exact GraphTables.relationAt_relationOf _ _ _

theorem relation_reverse (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot (!orientation)) b a =
      GraphTables.relationAt (relation P selfLoop event slot orientation) a b := by
  simp only [relationAt_relation]
  cases orientation <;> rfl

/-- The old predicate is read in the same row-major order as a graph row. -/
def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

def relationFromTable (old : Vector Bool (q * q)) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable := relation (oldPredicate old) selfLoop event slot orientation

@[simp] theorem oldPredicate_relationAt (old : GraphTables.RelationTable)
    (a b : GraphTables.Label) : oldPredicate old a b = GraphTables.relationAt old a b := rfl

theorem relationFromTable_eq (old : GraphTables.RelationTable) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin 64)) (slot : Fin 6) (orientation : Bool) :
    relationFromTable old selfLoop event slot orientation =
      relation (GraphTables.relationAt old) selfLoop event slot orientation := rfl

section Semantics

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem eqProfile_query_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (i j : Fin 6) :
    eqProfile (decide (G.tail e = G.head e)) (query (G.accepts e) event) i j = true ↔
      (AlphabetGraph.verifier G).query (e, event) i =
        (AlphabetGraph.verifier G).query (e, event) j := by
  rw [← globalize_query G e event i, ← globalize_query G e event j]
  exact (globalize_eq_iff (G.tail e) (G.head e) e _ rfl _ _).symm

theorem canonicalSlot_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    canonicalSlot (decide (G.tail e = G.head e)) (query (G.accepts e) event) slot =
      QueryIncidence.canonicalSlot (AlphabetGraph.verifier G) (e, event) slot := by
  unfold canonicalSlot QueryIncidence.canonicalSlot
  apply Fin.find_congr'
  exact eqProfile_query_iff G e event _ slot

omit [DecidableEq E] in
theorem repeatedConsistent_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    RepeatedConsistent (decide (G.tail e = G.head e)) (query (G.accepts e) event) label ↔
      QueryIncidence.RepeatedConsistent (AlphabetGraph.verifier G) (e, event) label := by
  constructor
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mpr hij)
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mp hij)

omit [DecidableEq V] [DecidableEq E] in
theorem verifier_accepts (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    (AlphabetGraph.verifier G).accepts (e, event) label =
      AssignmentTester.eventAccepts event.1 label := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rfl

theorem incidenceAccept_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) :
    incidenceAccept (decide (G.tail e = G.head e)) (query (G.accepts e) event)
      (AssignmentTester.eventAccepts event.1) slot left right =
      QueryIncidence.incidenceAccept (AlphabetGraph.verifier G) (by decide) (e, event) slot
        left right := by
  simp only [incidenceAccept, QueryIncidence.incidenceAccept, QueryIncidence.LeftValid,
    verifier_accepts, repeatedConsistent_iff, canonicalSlot_eq,
    QueryIncidence.decodeRight, QueryIncidence.zeroSlot]
  rfl

/-- Every stored bit is the actual six-query incidence predicate under the
canonical explicit six-bit label enumeration, including loops and repeats. -/
theorem relationAt_relation_graph (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt
        (relation (G.accepts e) (decide (G.tail e = G.head e)) event slot orientation) a b =
      (AlphabetGraph.graph G).accepts (((e, event), slot), orientation)
        (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  rw [relationAt_relation]
  cases orientation <;>
    exact incidenceAccept_eq G e event slot _ _

end Semantics

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations

end

end OAI
