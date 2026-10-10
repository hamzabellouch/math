import OAI.Computability.FiniteCompiler.Transition

namespace OAI

/-!
Finite tape validation, scan reversal, and bounded cleanup.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Validator

section
open Relation

/-- The validator states I,J,J',N,V and its fresh machine handoff. -/
inductive Head
  | initial | left | right | workspace | suffix | start
  deriving DecidableEq

/-- A cell includes every tag field, even unused ones. -/
abbrev Cell (S Γ : Type*) := Base S × Tag S Γ

def cell {S Γ : Type*} (blank : Γ) (base : Base S) : Cell S Γ :=
  (base, clean blank)

/-- A headed sector in zipper notation. The left list is in reverse order,
    so its head is exactly the cell adjacent to the validator. -/
structure Sector (S Γ : Type*) where
  head : Head
  left : List (Cell S Γ)
  right : List (Cell S Γ)
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

/-- Literal internal equations compiler-validation, oriented as in the source.
    There is no entry from P and no transition from the machine back here. -/
inductive Step {S Γ : Type*} (blank : Γ) : Sector S Γ → Sector S Γ → Prop
  | initial_workspace (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.initial, cell blank .workspace :: l, r, lb, rb⟩
        ⟨.initial, l, cell blank .workspace :: r, lb, rb⟩
  | initial_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.initial, cell blank .cutC :: l, r, lb, rb⟩
        ⟨.left, l, cell blank .cutC :: r, lb, rb⟩
  | left_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.left, cell blank (.anchor a) :: l, r, lb, rb⟩
        ⟨.left, l, cell blank (.anchor a) :: r, lb, rb⟩
  | left_boundary (r : List (Cell S Γ)) (rb : Bool) :
      Step blank ⟨.left, [], r, true, rb⟩ ⟨.right, [], r, true, rb⟩
  | right_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.right, l, cell blank (.anchor a) :: r, lb, rb⟩
        ⟨.right, cell blank (.anchor a) :: l, r, lb, rb⟩
  | right_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.right, l, cell blank .cutC :: r, lb, rb⟩
        ⟨.workspace, cell blank .cutC :: l, r, lb, rb⟩
  | workspace (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.workspace, l, cell blank .workspace :: r, lb, rb⟩
        ⟨.workspace, cell blank .workspace :: l, r, lb, rb⟩
  | workspace_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.workspace, l, cell blank .cutD :: r, lb, rb⟩
        ⟨.suffix, cell blank .cutD :: l, r, lb, rb⟩
  | suffix_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.suffix, l, cell blank (.anchor a) :: r, lb, rb⟩
        ⟨.suffix, cell blank (.anchor a) :: l, r, lb, rb⟩
  | suffix_boundary (l : List (Cell S Γ)) (lb : Bool) :
      Step blank ⟨.suffix, l, [], lb, true⟩ ⟨.start, l, [], lb, true⟩

theorem step_deterministic {S Γ : Type*} (blank : Γ) :
    Relator.RightUnique (@Step S Γ blank) := by
  intro a b c hab hac
  cases hab <;> cases hac <;> rfl

/-- Validator reverse determinism, not asserted for machine phases. -/
theorem step_leftUnique {S Γ : Type*} (blank : Γ) :
    Relator.LeftUnique (@Step S Γ blank) := by
  intro a b c hac hbc
  cases hac <;> cases hbc <;> rfl

/-- An entry has clean D immediately right of its I head. -/
def Entry {S Γ : Type*} (blank : Γ) (s : Sector S Γ) : Prop :=
  s.head = .initial ∧ ∃ r, s.right = cell blank .cutD :: r

theorem entry_no_predecessor {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hb : Entry blank b) : ¬ Step blank a b := by
  rintro h
  rcases hb with ⟨hh, r, hr⟩
  cases h <;> simp_all [cell]

/-- Ordered cells and both flags are preserved by every internal validator step. -/
def skeleton {S Γ : Type*} (s : Sector S Γ) :
    List (Cell S Γ) × Bool × Bool :=
  (s.left.reverse ++ s.right, s.leftBoundary, s.rightBoundary)

theorem step_skeleton {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hab : Step blank a b) : skeleton a = skeleton b := by
  cases hab <;> simp [skeleton, List.reverse_cons, List.append_assoc]

theorem reaches_skeleton {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hab : ReflTransGen (Step blank) a b) : skeleton a = skeleton b := by
  induction hab with
  | refl => rfl
  | tail _ h ih => exact ih.trans (step_skeleton blank h)

open Relation
variable {S Γ : Type*} (blank : Γ)

/-- Exact clean-anchor language; dirty tags are not accepted. -/
inductive Anchors : List (Cell S Γ) → Prop
  | nil : Anchors []
  | cons (a : S) {l} : Anchors l → Anchors (cell blank (.anchor a) :: l)

/-- The right suffix tested from N: clean workspace, D, then clean anchors. -/
inductive Tail : List (Cell S Γ) → Prop
  | cut {l} : Anchors blank l → Tail (cell blank .cutD :: l)
  | work {l} : Tail l → Tail (cell blank .workspace :: l)

/-- The right suffix tested from J': anchors, C, workspace, D, anchors. -/
inductive Body : List (Cell S Γ) → Prop
  | cut {l} : Tail blank l → Body (cell blank .cutC :: l)
  | anchor (a : S) {l} : Body l → Body (cell blank (.anchor a) :: l)

/-- The reversed left side tested from I: workspace, C, then anchors. -/
inductive Left : List (Cell S Γ) → Prop
  | cut {l} : Anchors blank l → Left (cell blank .cutC :: l)
  | work {l} : Left l → Left (cell blank .workspace :: l)

/-- Necessary future checks at each phase. Already-scanned cells need not be
    constrained: backwards propagation recovers exactly the checks made. -/
def Ready (s : Sector S Γ) : Prop :=
  match s.head with
  | .initial => s.leftBoundary = true ∧ s.rightBoundary = true ∧
      Left blank s.left ∧ Tail blank s.right
  | .left => s.leftBoundary = true ∧ s.rightBoundary = true ∧
      Anchors blank s.left ∧ Body blank s.right
  | .right => s.rightBoundary = true ∧ Body blank s.right
  | .workspace => s.rightBoundary = true ∧ Tail blank s.right
  | .suffix => s.rightBoundary = true ∧ Anchors blank s.right
  | .start => True

theorem ready_predecessor {a b : Sector S Γ} (h : Step blank a b) :
    Ready blank b → Ready blank a := by
  cases h with
  | initial_workspace l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .work hleft, ?_⟩
      cases hright with | work h => exact h
  | initial_cut l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .cut hleft, ?_⟩
      cases hright with | cut h => exact h
  | left_anchor c l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .cons c hleft, ?_⟩
      cases hright with | anchor _ h => exact h
  | left_boundary r rb =>
      rintro ⟨hr, hright⟩
      exact ⟨rfl, hr, .nil, hright⟩
  | right_anchor c l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .anchor c hright⟩
  | right_cut l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cut hright⟩
  | workspace l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .work hright⟩
  | workspace_cut l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cut hright⟩
  | suffix_anchor c l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cons c hright⟩
  | suffix_boundary l lb =>
      intro _
      exact ⟨rfl, .nil⟩

theorem reaches_ready {a b : Sector S Γ} (h : ReflTransGen (Step blank) a b) :
    Ready blank b → Ready blank a := by
  induction h with
  | refl => exact id
  | tail _ h ih => exact fun hb => ih (ready_predecessor blank h hb)

theorem anchors_iff (l : List (Cell S Γ)) :
    Anchors blank l ↔ ∃ x : List S, l = x.map (fun a => cell blank (.anchor a)) := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl⟩
    | cons a _ ih =>
        obtain ⟨x, rfl⟩ := ih
        exact ⟨a :: x, rfl⟩
  · rintro ⟨x, rfl⟩
    induction x with
    | nil => exact .nil
    | cons a x ih => exact .cons a ih

theorem left_iff (l : List (Cell S Γ)) :
    Left blank l ↔ ∃ (s : ℕ) (x : List S),
      l = List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: x.map (fun a => cell blank (.anchor a)) := by
  constructor
  · intro h
    induction h with
    | cut h =>
        obtain ⟨x, rfl⟩ := (anchors_iff blank _).mp h
        exact ⟨0, x, rfl⟩
    | work _ ih =>
        obtain ⟨s, x, rfl⟩ := ih
        exact ⟨s+1, x, by simp [List.replicate_succ]⟩
  · rintro ⟨s, x, rfl⟩
    induction s with
    | zero => exact .cut ((anchors_iff blank _).mpr ⟨x, rfl⟩)
    | succ s ih => simpa [List.replicate_succ] using Left.work ih

/-- Every entry which reaches handoff has the FULL clean form in the manuscript:
    both boundaries, all clean tags, anchors on each side, and one quota.
    In particular this is not a cleanliness assumption on the input. -/
theorem passing_entry {a b : Sector S Γ} (ha : Entry blank a)
    (hab : ReflTransGen (Step blank) a b) (hb : b.head = .start) :
    ∃ (x y : List S) (s : ℕ), a =
      ⟨.initial, List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun c => cell blank (.anchor c))).reverse,
        cell blank .cutD :: y.map (fun c => cell blank (.anchor c)), true, true⟩ := by
  have hready : Ready blank a := reaches_ready blank hab (by simp [Ready, hb])
  rcases a with ⟨head, l, r, lb, rb⟩
  rcases ha with ⟨rfl, r', rfl⟩
  rcases hready with ⟨rfl, rfl, hl, hr⟩
  obtain ⟨s, x, rfl⟩ := (left_iff blank _).mp hl
  cases hr with
  | cut h =>
      obtain ⟨y, rfl⟩ := (anchors_iff blank _).mp h
      exact ⟨x.reverse, y, s, by simp⟩

end

open Relation
variable {S Γ : Type*} (blank : Γ)

theorem initial_workspaces (s : ℕ) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.initial, List.replicate s (cell blank .workspace) ++ l, r, lb, rb⟩
      ⟨.initial, l, List.replicate s (cell blank .workspace) ++ r, lb, rb⟩ := by
  induction s generalizing r with
  | zero => exact .refl
  | succ s ih =>
      simp only [List.replicate_succ, List.cons_append]
      refine (ReflTransGen.single (Step.initial_workspace _ _ _ _)).trans ?_
      convert ih (cell blank .workspace :: r) using 1
      simp only [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem left_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.left, x.map (fun a => cell blank (.anchor a)) ++ l, r, lb, rb⟩
      ⟨.left, l, (x.map (fun a => cell blank (.anchor a))).reverse ++ r, lb, rb⟩ := by
  induction x generalizing r with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.left_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: r)

theorem right_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.right, l, x.map (fun a => cell blank (.anchor a)) ++ r, lb, rb⟩
      ⟨.right, (x.map (fun a => cell blank (.anchor a))).reverse ++ l, r, lb, rb⟩ := by
  induction x generalizing l with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.right_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: l)

theorem workspace_many (s : ℕ) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.workspace, l, List.replicate s (cell blank .workspace) ++ r, lb, rb⟩
      ⟨.workspace, List.replicate s (cell blank .workspace) ++ l, r, lb, rb⟩ := by
  induction s generalizing l with
  | zero => exact .refl
  | succ s ih =>
      simp only [List.replicate_succ, List.cons_append]
      refine (ReflTransGen.single (Step.workspace _ _ _ _)).trans ?_
      convert ih (cell blank .workspace :: l) using 1
      simp only [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem suffix_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.suffix, l, x.map (fun a => cell blank (.anchor a)) ++ r, lb, rb⟩
      ⟨.suffix, (x.map (fun a => cell blank (.anchor a))).reverse ++ l, r, lb, rb⟩ := by
  induction x generalizing l with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.suffix_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: l)

/-- Conversely every full clean entry passes the validator, with all cells
    left of the head at the handoff to the simulated program. -/
theorem clean_entry_reaches (x y : List S) (s : ℕ) :
    ReflTransGen (Step blank)
      ⟨.initial, List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse,
        cell blank .cutD :: y.map (fun a => cell blank (.anchor a)), true, true⟩
      ⟨.start, (y.map (fun a => cell blank (.anchor a))).reverse ++
        cell blank .cutD :: (List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse),
        [], true, true⟩ := by
  refine (initial_workspaces blank s _ _ true true).trans ?_
  refine (ReflTransGen.single (Step.initial_cut _ _ _ _)).trans ?_
  have hx := left_anchors blank x.reverse []
    (cell blank .cutC :: (List.replicate s (cell blank .workspace) ++
      cell blank .cutD :: y.map (fun a => cell blank (.anchor a)))) true true
  simp only [List.map_reverse, List.append_nil, List.reverse_reverse] at hx
  refine hx.trans ?_
  refine (ReflTransGen.single (Step.left_boundary _ _)).trans ?_
  refine (right_anchors blank x [] _ true true).trans ?_
  simp only [List.append_nil]
  refine (ReflTransGen.single (Step.right_cut _ _ _ _)).trans ?_
  refine (workspace_many blank s _ _ true true).trans ?_
  refine (ReflTransGen.single (Step.workspace_cut _ _ _ _)).trans ?_
  have hy := suffix_anchors blank y
    (cell blank .cutD :: (List.replicate s (cell blank .workspace) ++
      cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse)) [] true true
  simp only [List.append_nil] at hy
  refine hy.trans ?_
  simpa using ReflTransGen.single (Step.suffix_boundary _ true)

/-- A strictly decreasing validator measure, valid for every dirty sector. -/
def measure (s : Sector S Γ) : ℕ :=
  let k := s.left.length + s.right.length + 1
  match s.head with
  | .initial => 5*k + s.left.length
  | .left => 4*k + s.left.length
  | .right => 3*k + s.right.length
  | .workspace => 2*k + s.right.length
  | .suffix => k + s.right.length
  | .start => 0

theorem measure_decreases {a b : Sector S Γ} (h : Step blank a b) :
    measure b < measure a := by
  cases h <;> simp only [measure, List.length_cons, List.length_nil] <;> omega

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation
variable {α : Type*} {r : α → α → Prop}

/-- A source vertex cannot be reached from a different vertex. -/
theorem source_eq_of_reaches {a b : α} (hb : ∀ c, ¬ r c b)
    (hab : ReflTransGen r a b) : a = b := by
  rcases hab.cases_tail with h | ⟨c, _, hcb⟩
  · exact h.symm
  · exact False.elim (hb c hcb)

/-- In a reverse-deterministic graph, two sources reaching the same vertex agree. -/
theorem sources_unique_of_join (hr : Relator.LeftUnique r) {a b c : α}
    (ha : ∀ x, ¬ r x a) (hb : ∀ x, ¬ r x b)
    (hac : ReflTransGen r a c) (hbc : ReflTransGen r b c) : a = b := by
  induction hac with
  | refl => exact (source_eq_of_reaches ha hbc).symm
  | @tail c d hac hcd ih =>
      rcases hbc.cases_tail with h | ⟨x, hbx, hxd⟩
      · subst d
        exact False.elim (hb c hcd)
      · have hxc : c = x := hr hcd hxd
        subst x
        exact ih hbx

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
open Relation
variable {S Γ : Type*} (blank : Γ)

theorem entries_unique (a b : Sector S Γ) (ha : Entry blank a) (hb : Entry blank b)
    (hab : EqvGen (Step blank) a b) : a = b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins (step_deterministic blank) hab
  exact sources_unique_of_join (step_leftUnique blank)
    (fun _ => entry_no_predecessor blank ha) (fun _ => entry_no_predecessor blank hb) hac hbc

/-- The machine may alter tags but never these ordered bases or outer flags. -/
def baseSkeleton (s : Sector S Γ) : List (Base S) × Bool × Bool :=
  ((s.left.reverse ++ s.right).map Prod.fst, s.leftBoundary, s.rightBoundary)

theorem clean_anchors {l : List (Cell S Γ)} (h : Anchors blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | nil => rfl
  | cons a h ih => simpa [cell] using congrArg (cell blank (.anchor a) :: ·) ih

theorem clean_left {l : List (Cell S Γ)} (h : Left blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | cut h => simp only [List.map_cons, cell, clean_anchors blank h]
  | work h ih => simpa [cell] using congrArg (cell blank .workspace :: ·) ih

theorem clean_tail {l : List (Cell S Γ)} (h : Tail blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | cut h => simp only [List.map_cons, cell, clean_anchors blank h]
  | work h ih => simpa [cell] using congrArg (cell blank .workspace :: ·) ih

theorem cutD_not_mem_left {l : List (Cell S Γ)} (h : Left blank l) :
    cell blank .cutD ∉ l := by
  obtain ⟨s, x, rfl⟩ := (left_iff blank _).mp h
  simp [cell]

/-- Passing entries are determined by their invariant base sequence, with no
    injectivity hypothesis on the subsequent simulated-machine transitions. -/
theorem passing_entries_unique {a b : Sector S Γ}
    (ha : Entry blank a) (hb : Entry blank b)
    (hra : Ready blank a) (hrb : Ready blank b)
    (hs : baseSkeleton a = baseSkeleton b) : a = b := by
  rcases a with ⟨qa, la, ra, lba, rba⟩
  rcases b with ⟨qb, lb, rb, lbb, rbb⟩
  rcases ha with ⟨rfl, ra', rfl⟩
  rcases hb with ⟨rfl, rb', rfl⟩
  rcases hra with ⟨rfl, rfl, hal, har⟩
  rcases hrb with ⟨rfl, rfl, hbl, hbr⟩
  have hcells : la.reverse ++ cell blank .cutD :: ra' =
      lb.reverse ++ cell blank .cutD :: rb' := by
    have h := congrArg (fun z => z.1.map (cell blank)) hs
    simp only [baseSkeleton, List.map_append, List.map_reverse] at h
    simpa only [clean_left blank hal, clean_left blank hbl,
      clean_tail blank har, clean_tail blank hbr] using h
  have hnot : cell blank .cutD ∉ ra' := by
    cases har with
    | cut h =>
        obtain ⟨x, rfl⟩ := (anchors_iff blank _).mp h
        simp [cell]
  have hsplit := (List.append_cons_inj_of_notMem
    (by simpa using cutD_not_mem_left blank hal) hnot).mp hcells
  rcases hsplit with ⟨hl, _, hr⟩
  have hleft : la = lb := List.reverse_injective hl
  subst lb
  subst rb'
  rfl

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Validator.Extended
open Relation
variable {S Γ M : Type*} (blank : Γ)
abbrev Cfg (S Γ M : Type*) := Sector S Γ ⊕ M

/-- Only the fresh handoff and machine configurations participate in simulation;
    in particular there is no return to I,J,J',N,V. -/
def Active : Cfg S Γ M → Prop
  | .inl v => v.head = .start
  | .inr _ => True

/-- The internal graph consists of literal validator equations and simulator
    edges. These edges contain neither quota insertion nor exit to cleanup. -/
inductive Step (r : Cfg S Γ M → Cfg S Γ M → Prop) :
    Cfg S Γ M → Cfg S Γ M → Prop
  | validator {v w} : Validator.Step blank v w → Step r (.inl v) (.inl w)
  | machine {a b} : Active a → Active b → r a b → Step r a b

theorem validator_not_start {a b : Sector S Γ} (h : Validator.Step blank a b) :
    a.head ≠ .start := by
  cases h <;> simp

theorem deterministic {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : Relator.RightUnique r) : Relator.RightUnique (Step blank r) := by
  intro a b c hab hac
  cases hab with
  | validator hab =>
      cases hac with
      | validator hac => exact congrArg Sum.inl (Validator.step_deterministic blank hab hac)
      | machine ha _ _ => exact False.elim (validator_not_start blank hab ha)
  | machine ha _ hab =>
      cases hac with
      | validator hac => exact False.elim (validator_not_start blank hac ha)
      | machine _ _ hac => exact hr hab hac

/-- A path starting in the validator either stays there, or first reaches its
    fresh handoff. This explicitly excludes a dirty bypass of validation. -/
theorem path_decomposition {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a : Sector S Γ} {b : Cfg S Γ M} (h : ReflTransGen (Step blank r) (.inl a) b) :
    (∃ v, b = .inl v ∧ ReflTransGen (Validator.Step blank) a v) ∨
    ∃ v, ReflTransGen (Validator.Step blank) a v ∧ v.head = .start := by
  induction h with
  | refl => exact Or.inl ⟨a, rfl, .refl⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨v, rfl, hav⟩ | hv
      · cases hbc with
        | validator h => exact Or.inl ⟨_, rfl, hav.tail h⟩
        | machine hv _ _ => exact Or.inr ⟨v, hav, hv⟩
      · exact Or.inr hv

theorem reaches_active {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a : Sector S Γ} {b : Cfg S Γ M} (h : ReflTransGen (Step blank r) (.inl a) b)
    (hb : Active b) :
    ∃ v, ReflTransGen (Validator.Step blank) a v ∧ v.head = .start := by
  rcases path_decomposition blank h with ⟨v, rfl, hav⟩ | hv
  · exact ⟨v, hav, hb⟩
  · exact hv

/-- Pulling a path back from a non-handoff validator configuration never
    encounters a simulator edge. -/
theorem path_to_validator {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a c : Cfg S Γ M} (h : ReflTransGen (Step blank r) a c)
    {b : Sector S Γ} (hc : c = .inl b) (hb : b.head ≠ .start) :
    ∃ v, a = .inl v ∧ ReflTransGen (Validator.Step blank) v b := by
  induction h generalizing b with
  | refl => exact ⟨b, hc, .refl⟩
  | @tail c d hac hcd ih =>
      subst d
      cases hcd with
      | validator h =>
          obtain ⟨v, hav, hvc⟩ := ih rfl (validator_not_start blank h)
          exact ⟨v, hav, hvc.tail h⟩
      | machine _ hd _ => exact False.elim (hb hd)

variable (bases : M → List (Base S) × Bool × Bool)

def baseSkeleton : Cfg S Γ M → List (Base S) × Bool × Bool
  | .inl v => Validator.baseSkeleton v
  | .inr q => bases q

theorem step_bases {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Cfg S Γ M} (h : Step blank r a b) :
    baseSkeleton bases a = baseSkeleton bases b := by
  cases h with
  | validator h =>
      have h' := Validator.step_skeleton blank h
      exact congrArg (fun z => (z.1.map Prod.fst, z.2)) h'
  | machine _ _ h => exact hr _ _ h

theorem connected_bases {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Cfg S Γ M} (h : EqvGen (Step blank r) a b) :
    baseSkeleton bases a = baseSkeleton bases b := by
  induction h with
  | rel _ _ h => exact step_bases blank bases hr h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Entry uniqueness survives arbitrary reverse branching in the simulated
    machine. This is source Lemma compiler-components on all dirty sectors. -/
theorem entries_unique {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hdet : Relator.RightUnique r)
    (hbase : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Sector S Γ} (ha : Entry blank a) (hb : Entry blank b)
    (hab : EqvGen (Step blank r) (.inl a) (.inl b)) : a = b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins (deterministic blank hdet) hab
  have hsame : Validator.baseSkeleton a = Validator.baseSkeleton b :=
    connected_bases blank bases hbase hab
  have hactive (hc : Active c) : a = b := by
    obtain ⟨v, hav, hv⟩ := reaches_active blank hac hc
    obtain ⟨w, hbw, hw⟩ := reaches_active blank hbc hc
    apply passing_entries_unique blank ha hb _ _ hsame
    · apply reaches_ready blank hav
      simp [Ready, hv]
    · apply reaches_ready blank hbw
      simp [Ready, hw]
  cases c with
  | inr q => exact hactive trivial
  | inl v =>
      by_cases hv : v.head = .start
      · exact hactive hv
      · obtain ⟨a', heqa, hav⟩ := path_to_validator blank hac rfl hv
        obtain ⟨b', heqb, hbv⟩ := path_to_validator blank hbc rfl hv
        cases Sum.inl.inj heqa
        cases Sum.inl.inj heqb
        exact sources_unique_of_join (step_leftUnique blank)
          (fun _ => entry_no_predecessor blank ha)
          (fun _ => entry_no_predecessor blank hb) hav hbv

end FiniteAlgebraicEnvelopes.Compiler.Validator.Extended

namespace FiniteAlgebraicEnvelopes.Compiler.Scan

/-- A list zipper for the same finite-scan semantics. Left cells are nearest
    first. This representation permits induction on literal scan paths. -/
structure Sector (Head Base Tag : Type*) where
  left : List (Base × Tag)
  head : Head
  right : List (Base × Tag)
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

variable {H B T : Type*}

def step (table : Table H B T) (v : Sector H B T) : Option (Sector H B T) :=
  match table.direction v.head with
  | .left => match v.left with
    | (b,t) :: l => (table.cell v.head b t).map fun a =>
        if a.cross then { v with left := l, head := a.head, right := (b,a.tag) :: v.right }
        else { v with left := (b,a.tag) :: l, head := a.head }
    | [] => if v.leftBoundary then
        (table.boundary v.head).map fun q => { v with head := q } else none
  | .right => match v.right with
    | (b,t) :: r => (table.cell v.head b t).map fun a =>
        if a.cross then { v with left := (b,a.tag) :: v.left, head := a.head, right := r }
        else { v with head := a.head, right := (b,a.tag) :: r }
    | [] => if v.rightBoundary then
        (table.boundary v.head).map fun q => { v with head := q } else none

def Step (table : Table H B T) (v w : Sector H B T) : Prop := step table v = some w

theorem deterministic (table : Table H B T) : Relator.RightUnique (Step table) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

def baseSkeleton (v : Sector H B T) : List B × Bool × Bool :=
  ((v.left.reverse ++ v.right).map Prod.fst, v.leftBoundary, v.rightBoundary)

theorem step_skeleton (table : Table H B T) {v w : Sector H B T}
    (h : Step table v w) : baseSkeleton v = baseSkeleton w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  unfold Step step at h
  cases hd : table.direction q <;> simp only [hd] at h
  · cases l with
    | nil =>
      cases lb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · contradiction
      · cases hb : table.boundary q <;> simp only [hb, Option.map_none, Option.map_some] at h
        · contradiction
        · cases Option.some.inj h; rfl
    | cons a l =>
      rcases a with ⟨b,t⟩
      cases hc : table.cell q b t <;> simp only [hc, Option.map_none, Option.map_some] at h
      · contradiction
      · rename_i ins
        cases hm : ins.cross <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at h <;> cases Option.some.inj h <;>
          simp [baseSkeleton, List.reverse_cons, List.append_assoc]
  · cases r with
    | nil =>
      cases rb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · contradiction
      · cases hb : table.boundary q <;> simp only [hb, Option.map_none, Option.map_some] at h
        · contradiction
        · cases Option.some.inj h; rfl
    | cons a r =>
      rcases a with ⟨b,t⟩
      cases hc : table.cell q b t <;> simp only [hc, Option.map_none, Option.map_some] at h
      · contradiction
      · rename_i ins
        cases hm : ins.cross <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at h <;> cases Option.some.inj h <;>
          simp [baseSkeleton, List.reverse_cons, List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
