import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys

namespace OAI

section

namespace PerfectCompleteness.CanonicalEdges

open MixedSupport CanonicalKeys

variable {n : Nat} {Y Z : Type*}

noncomputable def coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) : Label slots (p ∘ f) :=
  evaluateLabel slots (p ∘ f) (ReducedPartition.representative (reduction slots f) f P)

@[simp] theorem restore_coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    restore slots (p ∘ f) (coarsen slots f p P) = p (restore slots f P) := by
  exact restore_evaluateLabel slots (p ∘ f)
    (ReducedPartition.representative (reduction slots f) f P)

theorem coarsen_eq_iff (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) (Q : Label slots (p ∘ f)) :
    coarsen slots f p P = Q ↔ p (restore slots f P) = restore slots (p ∘ f) Q := by
  constructor
  · intro h
    rw [← restore_coarsen slots f p P, h]
  · intro h
    apply restore_injective slots (p ∘ f)
    exact (restore_coarsen slots f p P).trans h

@[simp] theorem coarsen_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z) (x : Assignment slots) :
    coarsen slots f p (evaluateLabel slots f x) = evaluateLabel slots (p ∘ f) x := by
  apply (coarsen_eq_iff slots f p _ _).2
  rw [restore_evaluateLabel, restore_evaluateLabel]
  rfl

theorem coarsen_surjective (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) : Function.Surjective (coarsen slots f p) := by
  intro Q
  refine ⟨evaluateLabel slots f
    (ReducedPartition.representative (reduction slots (p ∘ f)) (p ∘ f) Q), ?_⟩
  rw [coarsen_evaluateLabel]
  exact ReducedPartition.label_representative (reduction slots (p ∘ f)) (p ∘ f) Q

theorem card_coarsen_fiber_le [Finite Y] (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z) (Q : Label slots (p ∘ f)) :
    Nat.card {P : Label slots f // coarsen slots f p P = Q} ≤
      Nat.card {y : Y // p y = restore slots (p ∘ f) Q} := by
  let restoreFiber : {P : Label slots f // coarsen slots f p P = Q} →
      {y : Y // p y = restore slots (p ∘ f) Q} :=
    fun P => ⟨restore slots f P.val, (coarsen_eq_iff slots f p P.val Q).1 P.property⟩
  apply Nat.card_le_card_of_injective restoreFiber
  intro P P' h
  apply Subtype.ext
  apply restore_injective slots f
  exact congrArg Subtype.val h

theorem coarsen_at_most_two [Finite Y] (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z)
    (hp : ∀ z, Nat.card {y : Y // p y = z} ≤ 2) (Q : Label slots (p ∘ f)) :
    Nat.card {P : Label slots f // coarsen slots f p P = Q} ≤ 2 :=
  (card_coarsen_fiber_le slots f p Q).trans (hp (restore slots (p ∘ f) Q))

theorem binaryDeletion_at_most_two [Finite Y] (slots : Fin n → Slot)
    (f : Assignment slots → Bool × Y) (Q : Label slots (Prod.snd ∘ f)) :
    Nat.card {P : Label slots f // coarsen slots f Prod.snd P = Q} ≤ 2 := by
  apply coarsen_at_most_two slots f Prod.snd
  intro y
  exact (CanonicalPartition.card_binaryDeletion_fiber y).le

theorem coarsen_transportLabel {slots projected : Fin n → Slot}
    (π : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y)
    (p : Y → Z) (P : Label slots (f ∘ projectionMap π)) :
    transportLabel π (p ∘ f) (coarsen slots (f ∘ projectionMap π) p P) =
      coarsen projected f p (transportLabel π f P) := by
  apply restore_injective projected (p ∘ f)
  calc
    restore projected (p ∘ f)
        (transportLabel π (p ∘ f) (coarsen slots (f ∘ projectionMap π) p P)) =
        restore slots ((p ∘ f) ∘ projectionMap π)
          (coarsen slots (f ∘ projectionMap π) p P) :=
      (restore_projection π (p ∘ f) _).symm
    _ = p (restore slots (f ∘ projectionMap π) P) :=
      restore_coarsen slots (f ∘ projectionMap π) p P
    _ = p (restore projected f (transportLabel π f P)) :=
      congrArg p (restore_projection π f P)
    _ = restore projected (p ∘ f) (coarsen projected f p (transportLabel π f P)) :=
      (restore_coarsen projected f p (transportLabel π f P)).symm

end PerfectCompleteness.CanonicalEdges

end

section

namespace PerfectCompleteness.CanonicalKeyShape

open ClauseSupport MixedSupport
open scoped Classical

noncomputable section

inductive Shape where
  | clause (signs : SourceClause.Triple)
  | bit
  deriving DecidableEq, Fintype

def erase : Slot → Shape
  | .clause _ _ signs => .clause signs
  | .bit _ => .bit

def dummy : Shape → Slot
  | .clause signs => .clause 0 (fun _ => 0) signs
  | .bit => .bit 0

@[simp] theorem erase_dummy (s : Shape) : erase (dummy s) = s := by
  cases s <;> rfl

def domainEquiv (s : Slot) : s.Domain ≃ (dummy (erase s)).Domain := by
  cases s <;> exact Equiv.refl _

instance dummyDomainFintype (s : Shape) : Fintype (dummy s).Domain := by
  cases s <;> dsimp [dummy, Slot.Domain] <;> infer_instance

def shape {I : Type*} (slots : I → Slot) : I → Shape := fun i => erase (slots i)

def dummySlots {I : Type*} (shapes : I → Shape) : I → Slot := fun i => dummy (shapes i)

instance dummyAssignmentFintype {I : Type*} [Fintype I] [DecidableEq I]
    (shapes : I → Shape) : Fintype (Assignment (dummySlots shapes)) := by
  change Fintype (∀ i : I, (dummy (shapes i)).Domain)
  infer_instance

def assignmentEquiv {I : Type*} (slots : I → Slot) :
    Assignment slots ≃ Assignment (dummySlots (shape slots)) where
  toFun x i := domainEquiv (slots i) (x i)
  invFun x i := (domainEquiv (slots i)).symm (x i)
  left_inv x := by funext i; exact (domainEquiv (slots i)).symm_apply_apply (x i)
  right_inv x := by funext i; exact (domainEquiv (slots i)).apply_symm_apply (x i)

@[simp] theorem assignmentEquiv_apply {I : Type*} (slots : I → Slot)
    (x : Assignment slots) (i : I) :
    assignmentEquiv slots x i = domainEquiv (slots i) (x i) := rfl

def transport {I Y : Type*} (slots : I → Slot) (f : Assignment slots → Y) :
    Assignment (dummySlots (shape slots)) → Y := f ∘ (assignmentEquiv slots).symm

@[simp] theorem transport_apply {I Y : Type*} (slots : I → Slot)
    (f : Assignment slots → Y) (x : Assignment slots) :
    transport slots f (assignmentEquiv slots x) = f x := by
  simp only [transport, Function.comp_apply, Equiv.symm_apply_apply]

theorem assignmentEquiv_update {I : Type*} [DecidableEq I]
    (slots : I → Slot) (x : Assignment slots) (i : I) (u : (slots i).Domain) :
    assignmentEquiv slots (Function.update x i u) =
      Function.update (assignmentEquiv slots x) i (domainEquiv (slots i) u) := by
  funext j
  exact Function.apply_update (fun i => domainEquiv (slots i)) x i u j

theorem sectionFunction_erasure {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) (i : I) :
    sectionFunction slots f i =
      pull (sectionFunction (dummySlots (shape slots)) (transport slots f) i)
        (assignmentEquiv slots) (domainEquiv (slots i)) := by
  funext context u
  change f (Function.update context i u) =
    f ((assignmentEquiv slots).symm
      (Function.update (assignmentEquiv slots context) i (domainEquiv (slots i) u)))
  rw [← assignmentEquiv_update, Equiv.symm_apply_apply]

theorem localReduction_erasure {C C' Y : Type*} (s : Slot)
    (f : C → (dummy (erase s)).Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) (u : s.Domain) :
    localReduction s (pull f context (domainEquiv s)) u =
      localReduction (dummy (erase s)) f (domainEquiv s u) := by
  cases s with
  | clause occurrence variableIDs signs =>
      exact unprojected_clause_reduction_eq f context hcontext u
  | bit variableID =>
      exact unprojected_bit_reduction_eq f context hcontext u

theorem reduction_erasure {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) (x : Assignment slots) :
    reduction slots f x =
      reduction (dummySlots (shape slots)) (transport slots f) (assignmentEquiv slots x) := by
  funext i
  change localReduction (slots i) (sectionFunction slots f i) (x i) = _
  rw [sectionFunction_erasure]
  exact localReduction_erasure (slots i)
    (sectionFunction (dummySlots (shape slots)) (transport slots f) i)
    (assignmentEquiv slots) (assignmentEquiv slots).surjective (x i)

theorem partition_erasure {n : Nat} {Y : Type*}
    (slots : Fin n → Slot) (f : Assignment slots → Y) :
    CanonicalKeys.partition slots f =
      CanonicalKeys.partition (dummySlots (shape slots)) (transport slots f) := by
  exact ReducedPartition.parts_eq_of_pullback (assignmentEquiv slots)
    (assignmentEquiv slots).surjective
    (reduction slots f) (reduction (dummySlots (shape slots)) (transport slots f))
    f (transport slots f) (reduction_erasure slots f)
    (fun x => (transport_apply slots f x).symm)

inductive SupportMode where
  | dropped
  | clauseBit (position : Fin 3)
  | full
  | bit
  deriving DecidableEq, Fintype

def mode {C Y : Type*} (s : Slot) : (C → s.Domain → Y) → SupportMode :=
  match s with
  | .clause _ _ _ => fun f =>
      match clauseMode f with
      | .dropped => .dropped
      | .bit i => .clauseBit i
      | .full => .full
  | .bit _ => fun f => if Unused f then .dropped else .bit

def recover : Slot → SupportMode → SlotKey
  | .clause _ variableIDs _, .clauseBit i => .bit (variableIDs i)
  | .clause occurrence _ signs, .full => .full occurrence signs
  | .bit variableID, .bit => .bit variableID
  | _, _ => .dropped

theorem localKey_recover {C Y : Type*} (s : Slot) (f : C → s.Domain → Y) :
    localKey s f = recover s (mode s f) := by
  cases s with
  | clause occurrence variableIDs signs =>
      cases hmode : clauseMode f <;>
        simp only [localKey, clauseKey, mode, hmode, recover]
  | bit variableID =>
      change C → Bool → Y at f
      change (if Unused f then SlotKey.dropped else SlotKey.bit variableID) =
        recover (.bit variableID) (if Unused f then SupportMode.dropped else SupportMode.bit)
      by_cases h : Unused f <;> simp only [h, ite_true, ite_false, recover]

theorem mode_erasure {C C' Y : Type*} (s : Slot)
    (f : C → (dummy (erase s)).Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) :
    mode s (pull f context (domainEquiv s)) = mode (dummy (erase s)) f := by
  cases s with
  | clause occurrence variableIDs signs =>
      change C → Answer signs → Y at f
      change (match clauseMode (pull f context id) with
        | .dropped => SupportMode.dropped
        | .bit i => SupportMode.clauseBit i
        | .full => SupportMode.full) = _
      rw [unprojected_mode_eq f context hcontext]
      rfl
  | bit variableID =>
      change C → Bool → Y at f
      change (if Unused (pull f context id) then SupportMode.dropped else SupportMode.bit) =
        (if Unused f then SupportMode.dropped else SupportMode.bit)
      rw [unused_pull_iff f context id hcontext Function.surjective_id]

def modes {I Y : Type*} [DecidableEq I] (slots : I → Slot)
    (f : Assignment slots → Y) : I → SupportMode :=
  fun i => mode (slots i) (sectionFunction slots f i)

theorem modes_erasure {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) :
    modes slots f = modes (dummySlots (shape slots)) (transport slots f) := by
  funext i
  unfold modes
  rw [sectionFunction_erasure]
  exact mode_erasure (slots i)
    (sectionFunction (dummySlots (shape slots)) (transport slots f) i)
    (assignmentEquiv slots) (assignmentEquiv slots).surjective

theorem keyFields_recover {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) :
    keyFields slots f = fun i =>
      recover (slots i) (modes (dummySlots (shape slots)) (transport slots f) i) := by
  have hm := modes_erasure slots f
  funext i
  change localKey (slots i) (sectionFunction slots f i) = _
  rw [localKey_recover]
  change recover (slots i) (modes slots f i) = _
  rw [hm]

def retained {n : Nat} (slots : Fin n → Slot) (support : Fin n → SupportMode) :
    List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, recover (slots i) (support i)))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

theorem retainedKeys_recover {n : Nat} {Y : Type*}
    (slots : Fin n → Slot) (f : Assignment slots → Y) :
    retainedKeys slots f =
      retained slots (modes (dummySlots (shape slots)) (transport slots f)) := by
  simp only [retainedKeys, keyFields_recover, retained]

abbrev Input (n k : Nat) :=
  Σ shapes : Fin n → Shape, Assignment (dummySlots shapes) → Fin k

instance inputFintype (n k : Nat) : Fintype (Input n k) := by
  unfold Input
  infer_instance

def input {n k : Nat} (slots : Fin n → Slot) (f : Assignment slots → Fin k) : Input n k :=
  ⟨shape slots, transport slots f⟩

def inputPartition {n k : Nat} (data : Input n k) :
    Set (Set (Fin n → ReducedValue)) :=
  CanonicalKeys.partition (dummySlots data.1) data.2

def inputModes {n k : Nat} (data : Input n k) : Fin n → SupportMode :=
  modes (dummySlots data.1) data.2

theorem inputPartition_eq {n k : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Fin k) :
    inputPartition (input slots f) = CanonicalKeys.partition slots f :=
  (partition_erasure slots f).symm

theorem inputModes_recover {n k : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Fin k) :
    retained slots (inputModes (input slots f)) = retainedKeys slots f :=
  (retainedKeys_recover slots f).symm

end
end PerfectCompleteness.CanonicalKeyShape

end

section

namespace PerfectCompleteness.SourceKeys

open SourceClause MixedSupport CanonicalKeys

variable {v m n : Nat} {I Y Z : Type*}

inductive Endpoint (v m : Nat) where
  | clause (occurrence : Fin m)
  | variable (variableID : Fin v)
  deriving DecidableEq

def slot (clauses : Fin m → NormalizedClause v) : Endpoint v m → Slot
  | .clause c => .clause c.val (fun i => ((clauses c).variable i).val) (clauses c).signs
  | .variable j => .bit j.val

inductive Step (clauses : Fin m → NormalizedClause v) :
    Endpoint v m → Endpoint v m → Type
  | keep (s : Endpoint v m) : Step clauses s s
  | select (c : Fin m) (position : Fin 3) :
      Step clauses (.clause c) (.variable ((clauses c).variable position))

def Step.projection {clauses : Fin m → NormalizedClause v}
    {s t : Endpoint v m} : Step clauses s t → Projection (slot clauses s) (slot clauses t)
  | .keep s => .keep (slot clauses s)
  | .select c i => .select c.val (fun j => ((clauses c).variable j).val) (clauses c).signs i

def stepProjection {clauses : Fin m → NormalizedClause v}
    {source target : I → Endpoint v m} (steps : ∀ i, Step clauses (source i) (target i)) :
    ∀ i, Projection (slot clauses (source i)) (slot clauses (target i)) :=
  fun i => (steps i).projection

theorem key_step (side : Side) (clauses : Fin m → NormalizedClause v)
    {source target : Fin n → Endpoint v m}
    (steps : ∀ i, Step clauses (source i) (target i))
    (f : Assignment (slot clauses ∘ target) → Y) :
    key side (slot clauses ∘ source) (f ∘ projectionMap (stepProjection steps)) =
      key side (slot clauses ∘ target) f :=
  key_projection side (stepProjection steps) f

def endpointValue (clauses : Fin m → NormalizedClause v) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (s : Endpoint v m) → (slot clauses s).Domain
  | .clause c => ⟨(clauses c).restrict assignment, by
      apply (mem_satisfyingTriples (clauses c).signs _).2
      rw [localEval_restrict]
      exact hsat c⟩
  | .variable j => assignment j

theorem coordinate_restrict (c : NormalizedClause v) (assignment : Fin v → Bool)
    (i : Fin 3) : (c.restrict assignment).at i = assignment (c.variable i) := by
  refine Fin.cases (by rfl) (fun j => ?_) i
  refine Fin.cases (by rfl) (fun k => ?_) j
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  rfl

theorem endpointValue_projection (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    {s t : Endpoint v m} (step : Step clauses s t) :
    step.projection.map (endpointValue clauses assignment hsat s) =
      endpointValue clauses assignment hsat t := by
  cases step with
  | keep s => rfl
  | select c i => exact coordinate_restrict (clauses c) assignment i

def realizingAssignment (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : I → Endpoint v m) : Assignment (slot clauses ∘ endpoints) :=
  fun i => endpointValue clauses assignment hsat (endpoints i)

theorem realizingAssignment_projection (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    {source target : I → Endpoint v m}
    (steps : ∀ i, Step clauses (source i) (target i)) :
    projectionMap (stepProjection steps) (realizingAssignment clauses assignment hsat source) =
      realizingAssignment clauses assignment hsat target := by
  funext i
  exact endpointValue_projection clauses assignment hsat (steps i)

theorem evaluated_label_step (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    {source target : Fin n → Endpoint v m}
    (steps : ∀ i, Step clauses (source i) (target i))
    (f : Assignment (slot clauses ∘ target) → Y) :
    transportLabel (stepProjection steps) f
        (evaluateLabel (slot clauses ∘ source) (f ∘ projectionMap (stepProjection steps))
          (realizingAssignment clauses assignment hsat source)) =
      evaluateLabel (slot clauses ∘ target) f
        (realizingAssignment clauses assignment hsat target) := by
  exact (evaluateLabel_projection (slots := slot clauses ∘ source)
    (projected := slot clauses ∘ target) (stepProjection steps) f
    (realizingAssignment clauses assignment hsat source)).trans
      (congrArg (evaluateLabel (slot clauses ∘ target) f)
        (realizingAssignment_projection clauses assignment hsat steps))

theorem evaluated_label_satisfies (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : Fin n → Endpoint v m) (f : Assignment (slot clauses ∘ endpoints) → Y)
    (p : Y → Z) :
    CanonicalEdges.coarsen (slot clauses ∘ endpoints) f p
        (evaluateLabel (slot clauses ∘ endpoints) f
          (realizingAssignment clauses assignment hsat endpoints)) =
      evaluateLabel (slot clauses ∘ endpoints) (p ∘ f)
        (realizingAssignment clauses assignment hsat endpoints) :=
  CanonicalEdges.coarsen_evaluateLabel _ f p _

end PerfectCompleteness.SourceKeys

end

end OAI
