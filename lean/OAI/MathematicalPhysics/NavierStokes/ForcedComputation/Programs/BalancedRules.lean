import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Recorder
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RadixEncoding

namespace OAI

/-! The balanced three-stack table in paper 379-09, `balanced.tex`.
Every row preserves total prefix length, and its record identifies the
individual work-step row.  The table acts on arbitrary independent tails. -/

namespace ForcedComputation.Balanced

open scoped BigOperators

variable {Q A : Type*}

inductive Record (Q A : Type*)
  | stay (q : Q) (a : A)
  | left (q : Q) (a c : A)
  | right (q : Q) (a c : A)
  | boundary (q : Q) (a : A)
  deriving DecidableEq, Fintype

inductive Symbol (Q A : Type*)
  | work (a : A)
  | marked (a : A)
  | boundary
  | record (r : Record Q A)
  deriving DecidableEq, Fintype

inductive Control (Q : Type*)
  | checkpoint (q : Q)
  | outward (q : Q)
  | inward (q : Q)
  | dispatch (q : Q)
  deriving DecidableEq, Fintype

inductive Row (Q A : Type*)
  | enter (q : Q) (a : A)
  | outward (q : Q) (c : A)
  | supply (q : Q)
  | inward (q : Q) (c : A)
  | restore (q : Q) (a : A)
  | stay (q : Q) (a : A)
  | left (q : Q) (a c : A)
  | right (q : Q) (a c : A)
  | boundary (q : Q) (a : A)
  deriving DecidableEq, Fintype

open ForcedComputation.Balanced.Symbol

def Row.Allowed (M : Recorder.Machine Q A) : Row Q A → Prop
  | .enter q _ => M.halting q = false
  | .stay q a => M.move q a = 0
  | .left q a _ => M.move q a = -1
  | .right q a _ => M.move q a = 1
  | .boundary q a => M.move q a = 1
  | _ => True

def Row.sourceControl : Row Q A → Control Q
  | .enter q _ => .checkpoint q
  | .outward q _ | .supply q => .outward q
  | .inward q _ | .restore q _ => .inward q
  | .stay q _ | .left q _ _ | .right q _ _ | .boundary q _ => .dispatch q

def Row.targetControl (M : Recorder.Machine Q A) : Row Q A → Control Q
  | .enter q _ | .outward q _ => .outward q
  | .supply q | .inward q _ => .inward q
  | .restore q _ => .dispatch q
  | .stay q a | .left q a _ | .right q a _ | .boundary q a => .checkpoint (M.next q a)

def Row.sourcePrefixes (blank : A) : Row Q A → Fin 3 → List (Symbol Q A)
  | .enter _ a => ![[], [work a], []]
  | .outward _ c => ![[], [work c], []]
  | .supply _ => ![[], [.boundary, work blank], []]
  | .inward _ c => ![[work c], [], []]
  | .restore _ a => ![[marked a], [], []]
  | .stay _ a => ![[], [work a], [work blank]]
  | .left _ a c => ![[work c], [work a], [work blank]]
  | .right _ a c => ![[], [work a, work c], [work blank]]
  | .boundary _ a => ![[], [work a, .boundary, work blank], [work blank]]

def Row.targetPrefixes (M : Recorder.Machine Q A) (blank : A) :
    Row Q A → Fin 3 → List (Symbol Q A)
  | .enter _ a => ![[marked a], [], []]
  | .outward _ c => ![[work c], [], []]
  | .supply _ => ![[], [.boundary], [work blank]]
  | .inward _ c => ![[], [work c], []]
  | .restore _ a => ![[], [work a], []]
  | .stay q a => ![[], [work (M.write q a)], [record (.stay q a)]]
  | .left q a c => ![[], [work c, work (M.write q a)], [record (.left q a c)]]
  | .right q a c => ![[work (M.write q a)], [work c], [record (.right q a c)]]
  | .boundary q a => ![[work (M.write q a)], [work blank, .boundary], [record (.boundary q a)]]

/-- Balance is an identity for the complete table, without assumptions on tails. -/
theorem Row.balanced (M : Recorder.Machine Q A) (blank : A) (r : Row Q A) :
    (∑ j : Fin 3, (r.sourcePrefixes blank j).length) =
      ∑ j : Fin 3, (r.targetPrefixes M blank j).length := by
  cases r <;> simp [Row.sourcePrefixes, Row.targetPrefixes, Fin.sum_univ_succ]

abbrev Stack (Q A : Type*) := ℕ → Symbol Q A
abbrev Tails (Q A : Type*) := Fin 3 → Stack Q A

structure Configuration (Q A : Type*) where
  control : Control Q
  tapes : Tails Q A

def prefixConfiguration (q : Control Q) (words : Fin 3 → List (Symbol Q A))
    (tails : Tails Q A) : Configuration Q A :=
  ⟨q, fun j => Radix.prependWord (words j) (tails j)⟩

def Row.source (blank : A) (r : Row Q A) (tails : Tails Q A) : Configuration Q A :=
  prefixConfiguration r.sourceControl (r.sourcePrefixes blank) tails

def Row.target (M : Recorder.Machine Q A) (blank : A) (r : Row Q A)
    (tails : Tails Q A) : Configuration Q A :=
  prefixConfiguration (r.targetControl M) (r.targetPrefixes M blank) tails

/-- A row replaces exactly its three specified prefixes and preserves every tail. -/
def Step (M : Recorder.Machine Q A) (blank : A)
    (x y : Configuration Q A) : Prop :=
  ∃ r : Row Q A, r.Allowed M ∧ ∃ tails, x = r.source blank tails ∧ y = r.target M blank tails

theorem Row.step {M : Recorder.Machine Q A} {blank : A} {r : Row Q A}
    (hr : r.Allowed M) (tails : Tails Q A) :
    Step M blank (r.source blank tails) (r.target M blank tails) :=
  ⟨r, hr, tails, rfl, rfl⟩

/-- Finite words followed by an independent infinite tail decompose uniquely. -/
theorem prependWord_injective (w : List (Symbol Q A)) :
    Function.Injective (Radix.prependWord w) := by
  induction w with
  | nil => exact fun _ _ h => h
  | cons a w ih =>
    intro u v h
    apply ih
    funext n
    exact congrFun h (n + 1)

theorem Row.source_tails_injective (blank : A) (r : Row Q A) :
    Function.Injective (r.source blank) := by
  intro u v h
  funext j
  apply prependWord_injective (r.sourcePrefixes blank j)
  exact congrArg (fun c : Configuration Q A => c.tapes j) h

theorem Row.target_tails_injective (M : Recorder.Machine Q A) (blank : A) (r : Row Q A) :
    Function.Injective (r.target M blank) := by
  intro u v h
  funext j
  apply prependWord_injective (r.targetPrefixes M blank j)
  exact congrArg (fun c : Configuration Q A => c.tapes j) h

/-- Every target control specifies the stack whose top identifies the incoming row. -/
def targetKey (c : Configuration Q A) : Control Q × Symbol Q A :=
  (c.control, match c.control with
    | .checkpoint _ => c.tapes 2 0
    | .outward _ => c.tapes 0 0
    | .inward _ => c.tapes 1 0
    | .dispatch _ => c.tapes 1 0)

def Row.targetKey (M : Recorder.Machine Q A) : Row Q A → Control Q × Symbol Q A
  | .enter q a => (.outward q, marked a)
  | .outward q c => (.outward q, work c)
  | .supply q => (.inward q, .boundary)
  | .inward q c => (.inward q, work c)
  | .restore q a => (.dispatch q, work a)
  | .stay q a => (.checkpoint (M.next q a), record (.stay q a))
  | .left q a c => (.checkpoint (M.next q a), record (.left q a c))
  | .right q a c => (.checkpoint (M.next q a), record (.right q a c))
  | .boundary q a => (.checkpoint (M.next q a), record (.boundary q a))

theorem Row.targetKey_eq (M : Recorder.Machine Q A) (blank : A)
    (r : Row Q A) (tails : Tails Q A) :
    Balanced.targetKey (r.target M blank tails) = r.targetKey M := by
  cases r <;> simp [Balanced.targetKey, Row.target, prefixConfiguration, Row.targetControl,
    Row.targetPrefixes, Row.targetKey, Radix.prependWord, Radix.prepend]

theorem Row.targetKey_injective (M : Recorder.Machine Q A) :
    Function.Injective (Row.targetKey M) := by
  intro r s h
  cases r <;> cases s <;> simp_all [Row.targetKey]

/-- Incoming branches are disjoint for arbitrary independent stack tails. -/
theorem Row.target_rows_eq (M : Recorder.Machine Q A) (blank : A)
    {r s : Row Q A} {u v : Tails Q A}
    (h : r.target M blank u = s.target M blank v) : r = s := by
  apply Row.targetKey_injective M
  simpa only [Row.targetKey_eq] using congrArg Balanced.targetKey h

/-- The complete target state recovers both the row and all three original tails. -/
theorem Row.target_unique (M : Recorder.Machine Q A) (blank : A)
    {r s : Row Q A} {u v : Tails Q A}
    (h : r.target M blank u = s.target M blank v) : r = s ∧ u = v := by
  have hrs := Row.target_rows_eq M blank h
  subst s
  exact ⟨rfl, r.target_tails_injective M blank h⟩

/-- A finite source decoder.  It need not accept malformed configurations;
on each guarded source cylinder it recovers the unique table row. -/
def decodeSource (M : Recorder.Machine Q A) (c : Configuration Q A) : Option (Row Q A) :=
  match c.control with
  | .checkpoint q => match c.tapes 1 0 with
    | .work a => some (.enter q a)
    | _ => none
  | .outward q => match c.tapes 1 0 with
    | .work a => some (.outward q a)
    | .boundary => some (.supply q)
    | _ => none
  | .inward q => match c.tapes 0 0 with
    | .work a => some (.inward q a)
    | .marked a => some (.restore q a)
    | _ => none
  | .dispatch q => match c.tapes 1 0 with
    | .work a =>
      if M.move q a = 0 then some (.stay q a)
      else if M.move q a = -1 then
        match c.tapes 0 0 with
        | .work b => some (.left q a b)
        | _ => none
      else match c.tapes 1 1 with
        | .work b => some (.right q a b)
        | .boundary => some (.boundary q a)
        | _ => none
    | _ => none

theorem Row.decode_source {M : Recorder.Machine Q A} {blank : A}
    {r : Row Q A} (hr : r.Allowed M) (tails : Tails Q A) :
    decodeSource M (r.source blank tails) = some r := by
  cases r <;> simp_all [decodeSource, Row.source, prefixConfiguration, Row.sourceControl,
    Row.sourcePrefixes, Row.Allowed, Radix.prependWord, Radix.prepend]

/-- Outgoing guarded branches are disjoint on the complete tail domains. -/
theorem Row.source_rows_eq {M : Recorder.Machine Q A} {blank : A}
    {r s : Row Q A} (hr : r.Allowed M) (hs : s.Allowed M) {u v : Tails Q A}
    (h : r.source blank u = s.source blank v) : r = s := by
  have hh := congrArg (decodeSource M) h
  rw [r.decode_source hr, s.decode_source hs] at hh
  exact Option.some.inj hh

theorem Step.deterministic {M : Recorder.Machine Q A} {blank : A}
    {x y z : Configuration Q A} (hy : Step M blank x y) (hz : Step M blank x z) : y = z := by
  obtain ⟨r, hr, u, rfl, rfl⟩ := hy
  obtain ⟨s, hs, v, he, rfl⟩ := hz
  have hrs := Row.source_rows_eq hr hs he
  subst s
  have huv := r.source_tails_injective blank he
  rw [huv]

theorem Step.predecessor_unique {M : Recorder.Machine Q A} {blank : A}
    {x y z : Configuration Q A} (hx : Step M blank x z) (hy : Step M blank y z) : x = y := by
  obtain ⟨r, hr, u, rfl, rfl⟩ := hx
  obtain ⟨s, hs, v, rfl, he⟩ := hy
  have huv := Row.target_unique M blank he
  rcases huv with ⟨hrs, huv⟩
  subst s
  subst v
  rfl

end ForcedComputation.Balanced

end OAI
