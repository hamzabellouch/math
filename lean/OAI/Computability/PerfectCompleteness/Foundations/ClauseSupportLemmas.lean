import OAI.Computability.PerfectCompleteness.Foundations.PartitionsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.SourceClause

namespace OAI

section

namespace PerfectCompleteness.ClauseSupport

open SourceClause

variable {C C' D E Y Z : Type*}

abbrev Answer (signs : Triple) := {u : Triple // u ∈ satisfyingTriples signs}

def coordinate {signs : Triple} (i : Fin 3) (u : Answer signs) : Bool :=
  u.val.at i

theorem coordinate_surjective (signs : Triple) (i : Fin 3) :
    Function.Surjective (coordinate (signs := signs) i) := by
  intro b
  obtain ⟨u, hu, hb⟩ := SourceClause.coordinate_surjective signs i b
  exact ⟨⟨u, hu⟩, hb⟩

theorem pair_surjective (signs : Triple) (i j : Fin 3) (hij : i ≠ j)
    (a b : Bool) : ∃ u : Answer signs, coordinate i u = a ∧ coordinate j u = b := by
  obtain ⟨u, hu, hi, hj⟩ := SourceClause.pair_surjective signs i j hij a b
  exact ⟨⟨u, hu⟩, hi, hj⟩

instance (signs : Triple) : Nonempty (Answer signs) := by
  obtain ⟨u, _⟩ := coordinate_surjective signs 0 false
  exact ⟨u⟩

def Unused (f : C → D → Y) : Prop := ∀ c u v, f c u = f c v

def Factors (f : C → D → Y) (p : D → E) : Prop :=
  ∀ c u v, p u = p v → f c u = f c v

abbrev Reducible {signs : Triple} (f : C → Answer signs → Y) (i : Fin 3) :=
  Factors f (coordinate i)

theorem unused_of_two_reductions {signs : Triple} (f : C → Answer signs → Y)
    {i j : Fin 3} (hij : i ≠ j) (hi : Reducible f i) (hj : Reducible f j) :
    Unused f := by
  intro c u v
  obtain ⟨w, hw₁, hw₂⟩ := pair_surjective signs i j hij (coordinate i u) (coordinate j v)
  exact (hi c u w hw₁.symm).trans (hj c w v hw₂)

theorem used_reduction_unique {signs : Triple} (f : C → Answer signs → Y)
    (hused : ¬ Unused f) {i j : Fin 3} (hi : Reducible f i) (hj : Reducible f j) :
    i = j := by
  by_contra hij
  exact hused (unused_of_two_reductions f hij hi hj)

def pull (f : C → D → Y) (context : C' → C) (localMap : E → D) : C' → E → Y :=
  fun c u => f (context c) (localMap u)

theorem unused_pull_iff (f : C → D → Y) (context : C' → C) (localMap : E → D)
    (hcontext : Function.Surjective context) (hlocal : Function.Surjective localMap) :
    Unused (pull f context localMap) ↔ Unused f := by
  constructor
  · intro h c u v
    obtain ⟨c', rfl⟩ := hcontext c
    obtain ⟨u', rfl⟩ := hlocal u
    obtain ⟨v', rfl⟩ := hlocal v
    exact h c' u' v'
  · intro h c u v
    exact h (context c) (localMap u) (localMap v)

theorem factors_pull_iff (f : C → D → Y) (context : C' → C) (localMap : E → D)
    (p : D → Z) (hcontext : Function.Surjective context)
    (hlocal : Function.Surjective localMap) :
    Factors (pull f context localMap) (p ∘ localMap) ↔ Factors f p := by
  constructor
  · intro h c u v huv
    obtain ⟨c', rfl⟩ := hcontext c
    obtain ⟨u', rfl⟩ := hlocal u
    obtain ⟨v', rfl⟩ := hlocal v
    exact h c' u' v' huv
  · intro h c u v huv
    exact h (context c) (localMap u) (localMap v) huv

theorem unused_kernel_invariant (f : C → D → Y) (g : C → D → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    Unused f ↔ Unused g := by
  exact ⟨fun h c u v => (hkernel c u v).1 (h c u v),
    fun h c u v => (hkernel c u v).2 (h c u v)⟩

theorem factors_kernel_invariant (f : C → D → Y) (g : C → D → Z) (p : D → E)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    Factors f p ↔ Factors g p := by
  exact ⟨fun h c u v hp => (hkernel c u v).1 (h c u v hp),
    fun h c u v hp => (hkernel c u v).2 (h c u v hp)⟩

inductive Mode where
  | dropped
  | bit (position : Fin 3)
  | full
  deriving DecidableEq

noncomputable def clauseMode {signs : Triple} (f : C → Answer signs → Y) : Mode := by
  classical
  exact if Unused f then .dropped else
    if h : ∃ i, Reducible f i then .bit h.choose else .full

theorem clauseMode_unused {signs : Triple} (f : C → Answer signs → Y)
    (h : Unused f) : clauseMode f = .dropped := by
  simp [clauseMode, h]

theorem clauseMode_bit {signs : Triple} (f : C → Answer signs → Y)
    (hused : ¬ Unused f) (i : Fin 3) (hi : Reducible f i) : clauseMode f = .bit i := by
  classical
  have hex : ∃ j, Reducible f j := ⟨i, hi⟩
  simp only [clauseMode, ite_eq_right hused, dite_eq_left hex]
  exact congrArg Mode.bit (used_reduction_unique f hused hex.choose_spec hi)

theorem clauseMode_full {signs : Triple} (f : C → Answer signs → Y)
    (hused : ¬ Unused f) (hfull : ¬ ∃ i, Reducible f i) : clauseMode f = .full := by
  simp [clauseMode, hused, hfull]

theorem clauseMode_eq_of_predicates {signs : Triple}
    (f : C → Answer signs → Y) (g : C' → Answer signs → Z)
    (hu : Unused f ↔ Unused g) (hr : ∀ i, Reducible f i ↔ Reducible g i) :
    clauseMode f = clauseMode g := by
  classical
  by_cases hf : Unused f
  · rw [clauseMode_unused f hf, clauseMode_unused g (hu.1 hf)]
  · have hg : ¬ Unused g := fun h => hf (hu.2 h)
    by_cases hred : ∃ i, Reducible f i
    · obtain ⟨i, hi⟩ := hred
      rw [clauseMode_bit f hf i hi, clauseMode_bit g hg i ((hr i).1 hi)]
    · have hn : ¬ ∃ i, Reducible g i := by
        rintro ⟨i, hi⟩
        exact hred ⟨i, (hr i).2 hi⟩
      rw [clauseMode_full f hf hred, clauseMode_full g hg hn]

theorem clauseMode_kernel_invariant {signs : Triple}
    (f : C → Answer signs → Y) (g : C → Answer signs → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    clauseMode f = clauseMode g :=
  clauseMode_eq_of_predicates f g (unused_kernel_invariant f g hkernel)
    (fun i => factors_kernel_invariant f g (coordinate i) hkernel)

theorem unprojected_mode_eq {signs : Triple} (f : C → Answer signs → Y)
    (context : C' → C) (hcontext : Function.Surjective context) :
    clauseMode (pull f context id) = clauseMode f := by
  apply clauseMode_eq_of_predicates
  · exact unused_pull_iff f context id hcontext Function.surjective_id
  · intro i
    exact factors_pull_iff f context id (coordinate i) hcontext Function.surjective_id

inductive ReducedValue where
  | dropped
  | bit (value : Bool)
  | full (value : Triple)
  deriving DecidableEq

def reduceByMode {signs : Triple} (mode : Mode) (u : Answer signs) : ReducedValue :=
  match mode with
  | .dropped => .dropped
  | .bit i => .bit (coordinate i u)
  | .full => .full u.val

noncomputable def clauseReduction {signs : Triple} (f : C → Answer signs → Y) :
    Answer signs → ReducedValue := reduceByMode (clauseMode f)

noncomputable def bitReduction (f : C → Bool → Y) (b : Bool) : ReducedValue := by
  classical
  exact if Unused f then .dropped else .bit b

theorem clauseReduction_sound {signs : Triple} (f : C → Answer signs → Y)
    (c : C) (u v : Answer signs) (h : clauseReduction f u = clauseReduction f v) :
    f c u = f c v := by
  classical
  by_cases hu : Unused f
  · exact hu c u v
  · by_cases hr : ∃ i, Reducible f i
    · obtain ⟨i, hi⟩ := hr
      have hm := clauseMode_bit f hu i hi
      have hc : coordinate i u = coordinate i v := by
        simpa only [clauseReduction, hm, reduceByMode, ReducedValue.bit.injEq] using h
      exact hi c u v hc
    · have hm := clauseMode_full f hu hr
      have hv : u.val = v.val := by
        simpa only [clauseReduction, hm, reduceByMode, ReducedValue.full.injEq] using h
      exact congrArg (f c) (Subtype.ext hv)

theorem bitReduction_sound (f : C → Bool → Y) (c : C) (u v : Bool)
    (h : bitReduction f u = bitReduction f v) : f c u = f c v := by
  classical
  by_cases hu : Unused f
  · exact hu c u v
  · have huv : u = v := by simpa [bitReduction, hu] using h
    exact congrArg (f c) huv

inductive SlotKey where
  | dropped
  | bit (variableID : Nat)
  | full (clauseOccurrence : Nat) (signs : Triple)
  deriving DecidableEq

noncomputable def clauseKey {signs : Triple} (occurrence : Nat) (variableIDs : Fin 3 → Nat)
    (f : C → Answer signs → Y) : SlotKey :=
  match clauseMode f with
  | .dropped => .dropped
  | .bit i => .bit (variableIDs i)
  | .full => .full occurrence signs

noncomputable def bitKey (variableID : Nat) (f : C → Bool → Y) : SlotKey := by
  classical
  exact if Unused f then .dropped else .bit variableID

theorem unprojected_clause_key_eq {signs : Triple} (f : C → Answer signs → Y)
    (context : C' → C) (hcontext : Function.Surjective context)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat) :
    clauseKey occurrence variableIDs (pull f context id) = clauseKey occurrence variableIDs f := by
  simp only [clauseKey, unprojected_mode_eq f context hcontext]

theorem unprojected_clause_reduction_eq {signs : Triple} (f : C → Answer signs → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (u : Answer signs) :
    clauseReduction (pull f context id) u = clauseReduction f u := by
  simp only [clauseReduction, unprojected_mode_eq f context hcontext]

theorem unprojected_bit_key_eq (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (variableID : Nat) :
    bitKey variableID (pull f context id) = bitKey variableID f := by
  classical
  simp only [bitKey, unused_pull_iff f context id hcontext Function.surjective_id]

theorem unprojected_bit_reduction_eq (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (b : Bool) :
    bitReduction (pull f context id) b = bitReduction f b := by
  classical
  simp only [bitReduction, unused_pull_iff f context id hcontext Function.surjective_id]

theorem projected_reducible {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (i : Fin 3) :
    Reducible (pull f context (coordinate (signs := signs) i)) i := by
  intro c u v h
  exact congrArg (f (context c)) h

theorem projected_unused_iff {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (i : Fin 3) :
    Unused (pull f context (coordinate (signs := signs) i)) ↔ Unused f :=
  unused_pull_iff f context (coordinate i) hcontext (coordinate_surjective signs i)

theorem projected_key_eq {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat) (i : Fin 3) :
    clauseKey occurrence variableIDs (pull f context (coordinate (signs := signs) i)) =
      bitKey (variableIDs i) f := by
  classical
  have hu := projected_unused_iff (signs := signs) f context hcontext i
  by_cases hf : Unused f
  · simp [clauseKey, clauseMode_unused _ (hu.2 hf), bitKey, hf]
  · have hp : ¬ Unused (pull f context (coordinate (signs := signs) i)) :=
      fun h => hf (hu.1 h)
    rw [clauseKey, clauseMode_bit _ hp i (projected_reducible f context i)]
    simp [bitKey, hf]

theorem projected_reduction_eq {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context)
    (i : Fin 3) (u : Answer signs) :
    clauseReduction (pull f context (coordinate i)) u = bitReduction f (coordinate i u) := by
  classical
  have hu := projected_unused_iff (signs := signs) f context hcontext i
  by_cases hf : Unused f
  · simp [clauseReduction, clauseMode_unused _ (hu.2 hf), reduceByMode, bitReduction, hf]
  · have hp : ¬ Unused (pull f context (coordinate (signs := signs) i)) :=
      fun h => hf (hu.1 h)
    rw [clauseReduction, clauseMode_bit _ hp i (projected_reducible f context i)]
    simp [reduceByMode, bitReduction, hf]

end PerfectCompleteness.ClauseSupport

end

section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {I C C' Y : Type*}

inductive Slot where
  | clause (occurrence : Nat) (variableIDs : Fin 3 → Nat) (signs : SourceClause.Triple)
  | bit (variableID : Nat)

def Slot.Domain : Slot → Type
  | .clause _ _ signs => Answer signs
  | .bit _ => Bool

instance (s : Slot) : Nonempty s.Domain := by
  cases s <;> dsimp [Slot.Domain] <;> infer_instance

abbrev Assignment (slots : I → Slot) := ∀ i, (slots i).Domain

inductive Projection : Slot → Slot → Type
  | keep (s : Slot) : Projection s s
  | select (occurrence : Nat) (variableIDs : Fin 3 → Nat)
      (signs : SourceClause.Triple) (position : Fin 3) :
      Projection (.clause occurrence variableIDs signs) (.bit (variableIDs position))

def Projection.map {s t : Slot} : Projection s t → s.Domain → t.Domain
  | .keep _ => id
  | .select _ _ _ i => coordinate i

theorem Projection.surjective {s t : Slot} (p : Projection s t) :
    Function.Surjective p.map := by
  cases p with
  | keep s => exact Function.surjective_id
  | select occurrence variableIDs signs i => exact coordinate_surjective signs i

def projectionMap {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) :
    Assignment slots → Assignment projected :=
  ProductReduction.productMap (fun i => (p i).map)

theorem projectionMap_surjective {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) :
    Function.Surjective (projectionMap p) :=
  ProductReduction.productMap_surjective _ (fun i => (p i).surjective)

variable [DecidableEq I]

theorem projectionMap_update {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i))
    (x : Assignment slots) (i : I) (u : (slots i).Domain) :
    projectionMap p (Function.update x i u) =
      Function.update (projectionMap p x) i ((p i).map u) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [projectionMap, ProductReduction.productMap]
  · simp [projectionMap, ProductReduction.productMap, Function.update_of_ne hji]

def sectionFunction (slots : I → Slot) (f : Assignment slots → Y) (i : I) :
    Assignment slots → (slots i).Domain → Y :=
  fun context u => f (Function.update context i u)

theorem sectionFunction_pullback {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i))
    (f : Assignment projected → Y) (i : I) :
    sectionFunction slots (f ∘ projectionMap p) i =
      pull (sectionFunction projected f i) (projectionMap p) (p i).map := by
  funext context u
  exact congrArg f (projectionMap_update p context i u)

noncomputable def localKey (s : Slot) : (C → s.Domain → Y) → SlotKey :=
  match s with
  | .clause occurrence variableIDs _ => clauseKey occurrence variableIDs
  | .bit variableID => bitKey variableID

noncomputable def localReduction (s : Slot) : (C → s.Domain → Y) → s.Domain → ReducedValue :=
  match s with
  | .clause _ _ _ => clauseReduction
  | .bit _ => bitReduction

theorem localReduction_sound (s : Slot) (f : C → s.Domain → Y)
    (c : C) (u v : s.Domain) (h : localReduction s f u = localReduction s f v) :
    f c u = f c v := by
  cases s with
  | clause occurrence variableIDs signs => exact clauseReduction_sound f c u v h
  | bit variableID => exact bitReduction_sound f c u v h

theorem localKey_projection {s t : Slot} (p : Projection s t)
    (f : C → t.Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) :
    localKey s (pull f context p.map) = localKey t f := by
  cases p with
  | keep s =>
    cases s with
    | clause occurrence variableIDs signs =>
      exact unprojected_clause_key_eq f context hcontext occurrence variableIDs
    | bit variableID => exact unprojected_bit_key_eq f context hcontext variableID
  | select occurrence variableIDs signs i =>
    exact projected_key_eq f context hcontext occurrence variableIDs i

theorem localReduction_projection {s t : Slot} (p : Projection s t)
    (f : C → t.Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) (u : s.Domain) :
    localReduction s (pull f context p.map) u = localReduction t f (p.map u) := by
  cases p with
  | keep s =>
    cases s with
    | clause occurrence variableIDs signs =>
      exact unprojected_clause_reduction_eq f context hcontext u
    | bit variableID => exact unprojected_bit_reduction_eq f context hcontext u
  | select occurrence variableIDs signs i =>
    exact projected_reduction_eq f context hcontext i u

noncomputable def keyFields (slots : I → Slot) (f : Assignment slots → Y) : I → SlotKey :=
  fun i => localKey (slots i) (sectionFunction slots f i)

noncomputable def coordinateReduction (slots : I → Slot) (f : Assignment slots → Y)
    (i : I) : (slots i).Domain → ReducedValue :=
  localReduction (slots i) (sectionFunction slots f i)

noncomputable def reduction (slots : I → Slot) (f : Assignment slots → Y) :
    Assignment slots → I → ReducedValue :=
  ProductReduction.productMap (coordinateReduction slots f)

theorem keyFields_projection {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    keyFields slots (f ∘ projectionMap p) = keyFields projected f := by
  funext i
  unfold keyFields
  rw [sectionFunction_pullback]
  exact localKey_projection (p i) (sectionFunction projected f i)
    (projectionMap p) (projectionMap_surjective p)

theorem reduction_projection {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i))
    (f : Assignment projected → Y) (x : Assignment slots) :
    reduction slots (f ∘ projectionMap p) x = reduction projected f (projectionMap p x) := by
  funext i
  change localReduction (slots i) (sectionFunction slots (f ∘ projectionMap p) i) (x i) = _
  rw [sectionFunction_pullback]
  exact localReduction_projection (p i) (sectionFunction projected f i)
    (projectionMap p) (projectionMap_surjective p) (x i)

theorem coordinateInvariant (slots : I → Slot) (f : Assignment slots → Y) :
    ProductReduction.CoordinateInvariant (coordinateReduction slots f) f := by
  apply ProductReduction.coordinateInvariant_of_update
  intro i x u h
  have hs := localReduction_sound (slots i) (sectionFunction slots f i) x (x i) u h
  simpa only [sectionFunction, Function.update_eq_self] using hs

theorem constant_on_reduction_fibers [Finite I]
    (slots : I → Slot) (f : Assignment slots → Y) {x x' : Assignment slots}
    (h : reduction slots f x = reduction slots f x') : f x = f x' :=
  ProductReduction.constant_on_product_fibers _ f (coordinateInvariant slots f) h

noncomputable def retainedKeys {n : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Y) : List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, keyFields slots f i))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

theorem retainedKeys_projection {n : Nat} {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    retainedKeys slots (f ∘ projectionMap p) = retainedKeys projected f := by
  simp only [retainedKeys, keyFields_projection]

end PerfectCompleteness.MixedSupport

end

end OAI
