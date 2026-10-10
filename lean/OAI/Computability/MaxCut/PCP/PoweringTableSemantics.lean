import Mathlib
import OAI.Computability.MaxCut.PCP.PoweringOpinionTables

namespace OAI


/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

section TableTransport

/-- Each enumerated directed occurrence evaluates its actual powering test. -/
theorem edgeSatisfied_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied
      (encodeLabeling d n labels) (encodeDart vertices d n e) =
        (mathematicalGraph input n).edgeSatisfied labels e := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel encodeDart
  simpa using!
    GenericGraphTables.enumeratedGraph_edgeSatisfied (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels e

/-- The equality also holds for every encoded assignment and every stored row. -/
theorem edgeSatisfied_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (i : Fin (dartCount vertices d n)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels i =
      (mathematicalGraph input n).edgeSatisfied (decodeLabeling d n labels)
        (decodeDart vertices d n i) := by
  have h := edgeSatisfied_encoded input n (decodeLabeling d n labels)
    (decodeDart vertices d n i)
  erw [encodeLabeling_decodeLabeling d n labels,
    encodeDart_decodeDart vertices d n i] at h
  exact h

/-- The stored Boolean test is exactly the path test at the recorded endpoints. -/
theorem edgeSatisfied_eq_path {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (direction : Bool)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels
      (encodeDart vertices d n (direction, w)) =
    PoweringTest.pathAccepts (PortTables.portGraph input) (PortTables.accepts input) n
      (finitePortSelector (PortTables.portGraph input) (n + 1)) w
      (decodeLabeling d n labels w.1)
      (decodeLabeling d n labels (endpoint (PortTables.portGraph input) w)) := by
  rw [edgeSatisfied_decoded input n labels (encodeDart vertices d n (direction, w)),
    decodeDart_encodeDart vertices d n (direction, w)]
  exact PoweringTest.poweredGraph_edgeSatisfied (PortTables.portGraph input)
    (PortTables.accepts input) n (finitePortSelector (PortTables.portGraph input) (n + 1))
    (decodeLabeling d n labels) direction w

/-- Exact rejected-dart counting, retaining both orientations and repeated walks. -/
theorem rejectionCount_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount
      (encodeLabeling d n labels) = (mathematicalGraph input n).rejectionCount labels := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel
  simpa using!
    GenericGraphTables.enumeratedGraph_rejectionCount (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels

theorem rejectionCount_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount labels =
      (mathematicalGraph input n).rejectionCount (decodeLabeling d n labels) := by
  have h := rejectionCount_encoded input n (decodeLabeling d n labels)
  erw [encodeLabeling_decodeLabeling d n labels] at h
  exact h

/-- The denominator equality comes from the same explicit dart bijection. -/
theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

/-- The table has a satisfying encoded assignment exactly when the powered graph does. -/
theorem satisfiable_iff {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    (GenericGraphTables.semantics (table input n)).Satisfiable ↔
      (mathematicalGraph input n).Satisfiable := by
  constructor
  · rintro ⟨labels, satisfies⟩
    refine ⟨decodeLabeling d n labels, ?_⟩
    intro e
    have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) e
    erw [encodeLabeling_decodeLabeling d n labels] at h
    exact h.symm.trans (satisfies (encodeDart vertices d n e))
  · rintro ⟨labels, satisfies⟩
    refine ⟨encodeLabeling d n labels, ?_⟩
    intro i
    have h := edgeSatisfied_encoded input n labels (decodeDart vertices d n i)
    rw [encodeDart_decodeDart vertices d n i] at h
    exact h.trans (satisfies (decodeDart vertices d n i))

/-- Perfect completeness from the actual stored base predicates. -/
theorem preserves_satisfiability {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (h : (PortTables.baseGraph input).Satisfiable) :
    (GenericGraphTables.semantics (table input n)).Satisfiable := by
  apply (satisfiable_iff input n).mpr
  exact PoweringTest.preserves_satisfiability (PortTables.portGraph input)
    (PortTables.accepts input) (PortTables.accepts_rotation input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1)) h

/-- The path rejection average equals the encoded table's actual rejection fraction. -/
theorem path_rejection_mean_eq_table_fraction {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (labels : EncodedLabeling vertices d n) :
    SpectralReturn.mean (fun w : Walk (Fin vertices) (Fin d) (n + 1) =>
      PoweringMoment.bit
        (PoweringTest.pathAccepts (PortTables.portGraph input) (PortTables.accepts input) n
          (finitePortSelector (PortTables.portGraph input) (n + 1)) w
          (decodeLabeling d n labels w.1)
          (decodeLabeling d n labels (endpoint (PortTables.portGraph input) w)) = false)) =
      ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) /
        ((table input n).darts : ℝ) := by
  rw [rejectionCount_decoded input n labels, ← card_darts_eq_table input n]
  exact PoweringCounting.path_rejection_mean_eq_count (PortTables.portGraph input)
    (PortTables.accepts input) n (finitePortSelector (PortTables.portGraph input) (n + 1))
    (decodeLabeling d n labels)

/-- Uniform actual rejection-count gaps are invariant under the executable encoding. -/
theorem uniform_count_gap_iff {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ) :
    (∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ)) ↔
    (∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) := by
  constructor
  · intro h labels
    have hlabels := h (encodeLabeling d n labels)
    erw [rejectionCount_encoded input n labels, ← card_darts_eq_table input n] at hlabels
    exact hlabels
  · intro h labels
    rw [rejectionCount_decoded input n labels]
    have hlabels := h (decodeLabeling d n labels)
    rw [card_darts_eq_table input n] at hlabels
    exact hlabels

/-- Apply an established powering count bound to every encoded table labeling. -/
theorem uniform_count_gap {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ)
    (hgap : ∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) :
    ∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) :=
  (uniform_count_gap_iff input n epsilon).mpr hgap

end TableTransport

end MaxCutGames.Foundations.PCP.PoweringTableSemantics


/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace MaxCutGames.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

theorem canonicalSlot_query [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) :
    T.query event (canonicalSlot T event i) = T.query event i :=
  Fin.find_spec (p := fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def incidenceAccept [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q) : Bool :=
  decide (LeftValid T event left) &&
    decide (left (canonicalSlot T event slot) = decodeRight positive right)

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

def predicate [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    Dart E q → Label q → Label q → Bool
  | ((event, slot), false), a, b => incidenceAccept T positive event slot a b
  | ((event, slot), true), a, b => incidenceAccept T positive event slot b a

def graph [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    ConstraintGraph (Vertex E X) (Dart E q) (Label q) where
  reverse := reverseEquiv
  reverse_involutive := reverse_involutive
  tail := tail T
  accepts := predicate T positive
  reverse_accepts := by
    rintro ⟨⟨event, slot⟩, orientation⟩ a b
    cases orientation <;> rfl

theorem edgeSatisfied_eq_incidence [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q)
    (event : E) (slot : Fin q) (orientation : Bool) :
    (graph T positive).edgeSatisfied labeling ((event, slot), orientation) =
      incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) := by
  cases orientation <;> rfl

def honestLabeling (T : Verifier E X q) (assignment : X → Bool) : Vertex E X → Label q
  | .inl event => response T assignment event
  | .inr address => encodeRight (assignment address)

theorem honest_leftValid (T : Verifier E X q) (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) :
    LeftValid T event (response T assignment event) := by
  refine ⟨accepted, ?_⟩
  intro i j hij
  exact congrArg assignment hij

theorem honest_incidence [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) (slot : Fin q) :
    incidenceAccept T positive event slot
      (honestLabeling T assignment (.inl event))
      (honestLabeling T assignment (.inr (T.query event slot))) = true := by
  simp only [incidenceAccept, Bool.and_eq_true, honestLabeling,
    decode_encodeRight]
  refine ⟨_root_.decide_eq_true (honest_leftValid T assignment event accepted), ?_⟩
  exact _root_.decide_eq_true (congrArg assignment (canonicalSlot_query T event slot))

theorem perfect_completeness [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool)
    (accepted : ∀ event, T.accepts event (response T assignment event) = true) :
    ∀ dart, (graph T positive).edgeSatisfied (honestLabeling T assignment) dart = true := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  rw [edgeSatisfied_eq_incidence]
  exact honest_incidence T positive assignment event (accepted event) slot

theorem satisfiable_of_verifier_satisfiable [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q)
    (sat : ∃ assignment : X → Bool,
      ∀ event, T.accepts event (response T assignment event) = true) :
    (graph T positive).Satisfiable := by
  obtain ⟨assignment, h⟩ := sat
  exact ⟨honestLabeling T assignment, perfect_completeness T positive assignment h⟩

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

theorem incidenceAccept_true [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q)
    (accepted : incidenceAccept T positive event slot left right = true) :
    T.accepts event left = true ∧ RepeatedConsistent T event left ∧
      left (canonicalSlot T event slot) = decodeRight positive right := by
  simp only [incidenceAccept, Bool.and_eq_true] at accepted
  have hvalid : LeftValid T event left := _root_.of_decide_eq_true accepted.1
  exact ⟨hvalid.1, hvalid.2, _root_.of_decide_eq_true accepted.2⟩

theorem all_incidences_imply_event [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (accepted : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true) :
    T.accepts event (response T (decodedAssignment positive labeling) event) = true := by
  have first := incidenceAccept_true T positive event (zeroSlot positive) _ _
    (accepted (zeroSlot positive))
  have labels_equal : labeling (.inl event) = response T (decodedAssignment positive labeling) event := by
    funext slot
    have info := incidenceAccept_true T positive event slot _ _ (accepted slot)
    exact (first.2.1 slot (canonicalSlot T event slot)
      (canonicalSlot_query T event slot).symm).trans info.2.2
  rw [← labels_equal]
  exact first.1

theorem rejected_event_forces_slot [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (rejected : T.accepts event (response T (decodedAssignment positive labeling) event) = false) :
    ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = false := by
  classical
  by_contra none
  have all : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true := by
    intro slot
    cases h : incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) with
    | false => exact False.elim (none ⟨slot, h⟩)
    | true => rfl
  have h := all_incidences_imply_event T positive labeling event all
  rw [rejected] at h
  cases h

def rejectedEvents [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Finset E :=
  Finset.univ.filter (fun event => T.accepts event (response T assignment event) = false)

def verifierRejectionCount [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Nat :=
  (rejectedEvents T assignment).card

/-- Every rejected event contributes two distinct rejected darts, one in each
orientation. A classical witness is used only in this counting proof. -/
theorem rejection_count_bound [Fintype E] [DecidableEq X]
    (T : Verifier E X q) (positive : 0 < q) (labeling : Vertex E X → Label q) :
    2 * verifierRejectionCount T (decodedAssignment positive labeling) ≤
      (graph T positive).rejectionCount labeling := by
  classical
  let failed := rejectedEvents T (decodedAssignment positive labeling)
  have witnesses : ∀ event, event ∈ failed →
      ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) = false := by
    intro event he
    apply rejected_event_forces_slot T positive labeling event
    simpa [failed, rejectedEvents] using he
  let chosen := fun event he => Classical.choose (witnesses event he)
  let inject : (failed.product (Finset.univ : Finset Bool)) →
      (graph T positive).rejectedDarts labeling := fun p =>
    ⟨((p.val.1, chosen p.val.1 (Finset.mem_product.mp p.property).1), p.val.2), by
      apply (ConstraintGraph.mem_rejectedDarts _ _ _).mpr
      rw [edgeSatisfied_eq_incidence]
      exact Classical.choose_spec (witnesses p.val.1 (Finset.mem_product.mp p.property).1)⟩
  have injective : Function.Injective inject := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d => d.val.1.1) h
    · exact congrArg (fun d => d.val.2) h
  have bound := Finset.card_le_card_of_injective injective
  simpa [failed, verifierRejectionCount, ConstraintGraph.rejectionCount,
    Finset.card_product, Nat.mul_comm] using bound

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

@[simp] theorem card_vertex [Fintype E] [Fintype X] :
    Fintype.card (Vertex E X) = Fintype.card E + Fintype.card X := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart [Fintype E] :
    Fintype.card (Dart E q) = 2 * q * Fintype.card E := by
  simp [Dart, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem gap_transfer [Fintype E] [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (a b : Nat)
    (sourceGap : ∀ assignment : X → Bool,
      a * Fintype.card E ≤ b * verifierRejectionCount T assignment)
    (labeling : Vertex E X → Label q) :
    a * Fintype.card (Dart E q) ≤ (b * q) * (graph T positive).rejectionCount labeling := by
  have source := Nat.mul_le_mul_left (2 * q) (sourceGap (decodedAssignment positive labeling))
  have incidences := Nat.mul_le_mul_left (b * q) (rejection_count_bound T positive labeling)
  rw [card_dart]
  calc
    a * (2 * q * Fintype.card E) = (2 * q) * (a * Fintype.card E) := by ac_rfl
    _ ≤ (2 * q) * (b * verifierRejectionCount T (decodedAssignment positive labeling)) := source
    _ = (b * q) * (2 * verifierRejectionCount T (decodedAssignment positive labeling)) := by ac_rfl
    _ ≤ (b * q) * (graph T positive).rejectionCount labeling := incidences

theorem six_query_alphabet : Fintype.card (Label 6) = 64 := by
  simp []

end MaxCutGames.Foundations.PCP.QueryIncidence



noncomputable section

namespace MaxCutGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open MaxCutGames.Foundations.Hastad

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_nonnegative (a b : Bool) : 0 ≤ disagreement a b := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_le_one (a b : Bool) : disagreement a b ≤ 1 := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_comm (a b : Bool) : disagreement a b = disagreement b a := by
  simp [disagreement, eq_comm]

theorem disagreement_triangle (a b c : Bool) :
    disagreement a c ≤ disagreement a b + disagreement b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagreement]

theorem disagreement_eq_sign (a b : Bool) :
    disagreement a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagreement, bitSign]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_nonnegative {X : Type*} [Fintype X] (f g : X → Bool) :
    0 ≤ relativeDistance f g :=
  Finset.expect_nonneg (fun _ _ => disagreement_nonnegative _ _)

theorem relativeDistance_comm {X : Type*} [Fintype X] (f g : X → Bool) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, disagreement_comm]

theorem relativeDistance_triangle {X : Type*} [Fintype X] (f g h : X → Bool) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  rw [relativeDistance, relativeDistance, relativeDistance,
    ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect (fun _ _ => disagreement_triangle _ _ _)

theorem relativeDistance_eq_sign {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Bool) :
    relativeDistance f g = (1 - 𝔼 x, bitSign (f x) * bitSign (g x)) / 2 := by
  simp only [relativeDistance, disagreement_eq_sign]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]
  simp

/-- The encoding is a literal coordinate read from a finite Boolean truth table. -/
def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

private def singletonMask_inline_CodeComposition {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

private theorem walsh_singletonMask_inline_CodeComposition {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (x : Cube A) : walsh (singletonMask_inline_CodeComposition a) x = bitSign (x a) := by
  classical
  unfold walsh singletonMask_inline_CodeComposition
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hba
    simp [hba, bitSign]
  · simp

private theorem singletonMask_ne_inline_CodeComposition {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    singletonMask_inline_CodeComposition a ≠ singletonMask_inline_CodeComposition b := by
  intro h
  have he := congrFun h a
  simp [singletonMask_inline_CodeComposition, hab] at he

theorem codeword_distance {A : Type*} [Fintype A] [DecidableEq A]
    {a b : A} (hab : a ≠ b) :
    relativeDistance (codeword a) (codeword b) = 1 / 2 := by
  rw [relativeDistance_eq_sign]
  have horth := walsh_orthogonality (singletonMask_inline_CodeComposition a) (singletonMask_inline_CodeComposition b)
  rw [ite_eq_right (singletonMask_ne_inline_CodeComposition hab)] at horth
  simp_rw [walsh_singletonMask_inline_CodeComposition] at horth
  change (1 - 𝔼 x : Cube A, bitSign (x a) * bitSign (x b)) / 2 = 1 / 2
  rw [horth]
  norm_num

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

/-- Classical choice is used only for the soundness analysis, not the output algorithm. -/
def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

theorem nearest_minimal {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) (a : A) :
    relativeDistance f (codeword (nearest f)) ≤ relativeDistance f (codeword a) :=
  Classical.choose_spec (exists_nearest f) a

theorem distance_from_other_codeword {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (f : Cube A → Bool) {a : A} (ha : a ≠ nearest f) :
    1 / 4 ≤ relativeDistance f (codeword a) := by
  have htri := relativeDistance_triangle (codeword (nearest f)) f (codeword a)
  rw [codeword_distance (Ne.symm ha), relativeDistance_comm (codeword (nearest f)) f] at htri
  have hmin := nearest_minimal f a
  linarith

/-- Two equal-sized blocks, indexed by a side bit and a common coordinate. -/
def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

theorem pairWord_distance {X : Type*} [Fintype X] [Nonempty X]
    (left right left' right' : X → Bool) :
    relativeDistance (pairWord left right) (pairWord left' right') =
      (relativeDistance left left' + relativeDistance right right') / 2 := by
  classical
  simp [relativeDistance, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Fintype.sum_prod_type, pairWord]
  ring

/-- Every satisfying encoded pair is far from a pair whose nearest decoding rejects. -/
theorem rejected_pair_far {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (accepts : A → A → Bool) (left right : Cube A → Bool)
    (hbad : accepts (nearest left) (nearest right) = false)
    (a b : A) (hgood : accepts a b = true) :
    1 / 8 ≤ relativeDistance (pairWord left right)
      (pairWord (codeword a) (codeword b)) := by
  rw [pairWord_distance]
  have hleft := relativeDistance_nonnegative left (codeword a)
  have hright := relativeDistance_nonnegative right (codeword b)
  by_cases ha : a = nearest left
  · have hb : b ≠ nearest right := by
      intro hb
      rw [ha, hb, hbad] at hgood
      cases hgood
    have hsep := distance_from_other_codeword right hb
    linarith
  · have hsep := distance_from_other_codeword left ha
    linarith

end MaxCutGames.Foundations.PCP.CodeComposition
end

end OAI
