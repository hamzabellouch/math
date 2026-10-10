import Mathlib

namespace OAI

/-!
Finite weak transition components and finite-scan instruction semantics.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation

variable {α : Type*} {r : α → α → Prop}

/-- An internal terminal configuration has no forward transition. -/
def Terminal (r : α → α → Prop) (a : α) : Prop := ∀ b, ¬ r a b

/-- Determinism makes forward-reachability joins an equivalence relation. -/
theorem deterministic_join (hr : Relator.RightUnique r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply equivalence_join_reflTransGen
  intro a b c hab hac
  have hbc := hr hab hac
  subst c
  exact ⟨b, .refl, .refl⟩

/-- Undirected internal connectivity may be converted to a common forward
    descendant; no reversibility of the simulated machine is required. -/
theorem weak_component_joins (hr : Relator.RightUnique r) {a b : α}
    (h : EqvGen r a b) : Join (ReflTransGen r) a b := by
  let : IsEquiv α (Join (ReflTransGen r)) := (deterministic_join hr).isEquiv
  exact EqvGen.eqvGen_le (fun _ y hxy => ⟨y, .single hxy, .refl⟩) _ _ h

theorem terminal_eq_of_reaches {a b : α} (ha : Terminal r a)
    (hab : ReflTransGen r a b) : a=b := by
  rcases hab.cases_head with h | ⟨c, hac, _⟩
  · exact h
  · exact False.elim (ha c hac)

/-- Every configuration in a terminal's weak component reaches that terminal.
    This is the graph-theoretic core of source Lemma compiler-components,
    and holds even without the finite-component assumption. -/
theorem reaches_terminal (hr : Relator.RightUnique r) {a b : α}
    (hb : Terminal r b) (hab : EqvGen r a b) : ReflTransGen r a b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins hr hab
  have h := terminal_eq_of_reaches hb hbc
  exact h ▸ hac

/-- In particular there cannot be two successful terminal sectors in the same
    weak component, even with arbitrary reverse branching on dirty data. -/
theorem terminal_unique (hr : Relator.RightUnique r) {a b : α}
    (ha : Terminal r a) (hb : Terminal r b) (hab : EqvGen r a b) : a=b :=
  terminal_eq_of_reaches ha (reaches_terminal hr hb hab)

/-- Fixed ordered bases, a head gap, and finite tags are the finite search data
    of the finite compiler. Workspace quota insertion is NOT an internal step. -/
structure Configuration (Head Tag : Type*) (k : ℕ) where
  head : Head
  gap : Fin (k+1)
  tags : Fin k → Tag
  deriving DecidableEq, Fintype

@[simp] theorem configuration_card (Head Tag : Type*) [Fintype Head] [Fintype Tag]
    (k : ℕ) : Fintype.card (Configuration Head Tag k) =
      (k+1) * Fintype.card Head * Fintype.card Tag ^ k := by
  let e : Configuration Head Tag k ≃ Head × Fin (k+1) × (Fin k → Tag) :=
    { toFun := fun c => (c.head, c.gap, c.tags)
      invFun := fun c => ⟨c.1, c.2.1, c.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Nat.mul_comm, Nat.mul_left_comm]

section FiniteSearch
variable [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- One effective expansion by undirected internal edges. -/
def expand (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, r a b ∨ r b a)

@[simp] theorem mem_expand (s : Finset α) (b : α) :
    b ∈ expand r s ↔ b ∈ s ∨ ∃ a ∈ s, r a b ∨ r b a := by
  simp [expand]

theorem subset_expand (s : Finset α) : s ⊆ expand r s :=
  fun _ h => (mem_expand r _ _).mpr (Or.inl h)

/-- This finite algorithm never calls the simulated partial function. -/
def search (a : α) : ℕ → Finset α
  | 0 => {a}
  | n+1 => expand r (search a n)

theorem search_mono (a : α) : Monotone (search r a) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_expand r _

theorem search_stabilizes (a : α) :
    search r a (Fintype.card α + 1) = search r a (Fintype.card α) := by
  have hs : ∀ n, (search r a n).card ≤ Fintype.card α :=
    fun _ => Finset.card_le_univ _
  have hm : Monotone (fun n => (search r a n).card) :=
    fun _ _ h => Finset.card_le_card (search_mono r a h)
  have hstep : ∀ n, (search r a n).card = (search r a (n+1)).card →
      (search r a (n+1)).card = (search r a (n+2)).card := by
    intro n hn
    have he : search r a n = search r a (n+1) :=
      Finset.eq_of_subset_of_card_le (search_mono r a (Nat.le_succ n)) hn.ge
    exact congrArg Finset.card (congrArg (expand r) he)
  exact (Finset.eq_of_subset_of_card_le
    (search_mono r a (Nat.le_succ (Fintype.card α)))
    (Nat.stabilises_of_monotone hm hs hstep (Nat.le_succ _)).le).symm

/-- Entire weak component, computed by at most the known number of vertices
    many finite expansions. Unlike running the machine, this always terminates. -/
def component (a : α) : Finset α := search r a (Fintype.card α)

theorem self_mem_component (a : α) : a ∈ component r a :=
  search_mono r a (Nat.zero_le _) (by simp [search])

theorem component_saturated (a b c : α) (hb : b ∈ component r a)
    (hbc : r b c ∨ r c b) : c ∈ component r a := by
  have h := (mem_expand r (component r a) c).mpr (Or.inr ⟨b, hb, hbc⟩)
  change c ∈ search r a (Fintype.card α + 1) at h
  rw [search_stabilizes] at h
  exact h

theorem mem_search_connected (a b : α) (n : ℕ) (h : b ∈ search r a n) :
    EqvGen r a b := by
  induction n generalizing b with
  | zero =>
    have : b=a := by simpa [search] using h
    subst b
    exact .refl a
  | succ n ih =>
    rcases (mem_expand r (search r a n) b).mp h with h | ⟨c, hc, hcb⟩
    · exact ih b h
    · refine EqvGen.trans _ _ _ (ih c hc) ?_
      rcases hcb with h | h
      · exact .rel _ _ h
      · exact .symm _ _ (.rel _ _ h)

/-- Exactness of the finite component search on malformed as well as genuine
    configurations. -/
theorem mem_component_iff (a b : α) : b ∈ component r a ↔ EqvGen r a b := by
  constructor
  · exact mem_search_connected r a b _
  · intro h
    have h' : ReflTransGen (SymmGen r) a b := by
      rw [EqvGen.reflTransGen_symmGen]
      exact h
    clear h
    induction h' with
    | refl => exact self_mem_component r a
    | @tail b c _ hbc ih => exact component_saturated r a b c ih hbc

/-- Consequently internal weak connectivity has a decision procedure that uses
    only the table and finite configuration data, not a halting oracle. -/
def decideConnected (a b : α) : Bool := decide (b ∈ component r a)

@[simp] theorem decideConnected_eq_true (a b : α) :
    decideConnected r a b = true ↔ EqvGen r a b := by
  simp [decideConnected, mem_component_iff]
end FiniteSearch

/- The actual finite-scan instruction semantics of the finite compiler.
   The immutable bases are not part of what an instruction may update. -/
inductive Base (S : Type*)
  | anchor : S → Base S
  | cutC : Base S
  | cutD : Base S
  | workspace : Base S
  deriving DecidableEq, Fintype

structure Tag (S Γ : Type*) where
  anchorRead : Bool
  workspaceFilled : Bool
  work : Γ
  outputRead : Bool
  output : Option S
  deriving DecidableEq, Fintype

/-- The same clean tag is used on every base, including its unused fields. -/
def clean {S Γ : Type*} (blank : Γ) : Tag S Γ :=
  ⟨false, false, blank, false, none⟩

inductive Direction
  | left | right
  deriving DecidableEq

instance : Fintype Direction := ⟨{.left, .right}, by intro x; cases x <;> simp⟩

structure Instruction (Head Tag : Type*) where
  head : Head
  tag : Tag
  cross : Bool
  deriving DecidableEq, Fintype

/-- Each state designates one reading side. A cell test has at most one result;
    boundary tests only change the state. A failed (or absent-boundary) test
    has no result. This is exactly the source's disjoint-case convention. -/
structure Table (Head Base Tag : Type*) where
  direction : Head → Direction
  cell : Head → Base → Tag → Option (Instruction Head Tag)
  boundary : Head → Option Head

/-- The finite state transition on sectors with fixed ordered base sequence.
    The two flags record whether alpha and omega are present. There is no
    insertion or deletion among internal steps. -/
def step {Head Base Tag : Type*} (table : Table Head Base Tag)
    {k : ℕ} (bases : Fin k → Base) (leftBoundary rightBoundary : Bool)
    (c : Configuration Head Tag k) : Option (Configuration Head Tag k) :=
  match table.direction c.head with
  | .right =>
    if hg : c.gap.val < k then
      let i : Fin k := ⟨c.gap.val, hg⟩
      (table.cell c.head (bases i) (c.tags i)).map fun a =>
        { head := a.head
          gap := if a.cross then ⟨c.gap.val+1, by omega⟩ else c.gap
          tags := Function.update c.tags i a.tag }
    else if rightBoundary then
      (table.boundary c.head).map fun q => { c with head := q }
    else none
  | .left =>
    if hg : 0 < c.gap.val then
      let i : Fin k := ⟨c.gap.val-1, by have := c.gap.isLt; omega⟩
      (table.cell c.head (bases i) (c.tags i)).map fun a =>
        { head := a.head
          gap := if a.cross then ⟨c.gap.val-1, by have := c.gap.isLt; omega⟩ else c.gap
          tags := Function.update c.tags i a.tag }
    else if leftBoundary then
      (table.boundary c.head).map fun q => { c with head := q }
    else none

/-- The relation used for component search; the equation is used both ways in
    the presentation, but only this direction in the deterministic analysis. -/
def InternalStep {Head Base Tag : Type*} (table : Table Head Base Tag)
    {k : ℕ} (bases : Fin k → Base) (leftBoundary rightBoundary : Bool)
    (c d : Configuration Head Tag k) : Prop :=
  step table bases leftBoundary rightBoundary c = some d

instance {Head Base Tag : Type*} [DecidableEq Head] [DecidableEq Tag]
    (table : Table Head Base Tag) {k : ℕ} (bases : Fin k → Base)
    (leftBoundary rightBoundary : Bool) :
    DecidableRel (InternalStep table bases leftBoundary rightBoundary) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Determinism is proved on ALL data, not assumed for clean initial sectors. -/
theorem internalStep_deterministic {Head Base Tag : Type*} (table : Table Head Base Tag)
    {k : ℕ} (bases : Fin k → Base) (leftBoundary rightBoundary : Bool) :
    Relator.RightUnique (InternalStep table bases leftBoundary rightBoundary) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

/-- The success-terminal assertion applies directly to the finite scan semantics. -/
theorem internal_terminal_reached {Head Base Tag : Type*} (table : Table Head Base Tag)
    {k : ℕ} (bases : Fin k → Base) (l r : Bool) {a b : Configuration Head Tag k}
    (hb : step table bases l r b = none)
    (hab : EqvGen (InternalStep table bases l r) a b) :
    ReflTransGen (InternalStep table bases l r) a b := by
  apply reaches_terminal (internalStep_deterministic table bases l r) _ hab
  intro c hc
  change step table bases l r b = some c at hc
  rw [hb] at hc
  cases hc

end FiniteAlgebraicEnvelopes.Compiler

end OAI
