import OAI.Computability.PerfectCompleteness.Foundations.ReducedDomains

namespace OAI

section

namespace PerfectCompleteness.DomainEncoding

open ClauseSupport ReducedDomains

variable {I C Y Z : Type*}

theorem allowed_dropped_iff (value : ReducedValue) :
    Allowed .dropped value ↔ value = .dropped := by
  cases value <;> simp [Allowed]

theorem legalAssignments_all_dropped :
    legalAssignments (fun _ : I => .dropped) = {fun _ : I => .dropped} := by
  ext values
  simp only [mem_legalAssignments, allowed_dropped_iff, Set.mem_singleton_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

theorem localKey_eq_dropped_of_unused (s : MixedSupport.Slot)
    (f : C → s.Domain → Y) (h : Unused f) :
    MixedSupport.localKey s f = .dropped := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
      change clauseKey occurrence variableIDs f = .dropped
      simp only [clauseKey, clauseMode_unused f h]
  | bit variableID =>
      change C → Bool → Y at f
      change Unused (D := Bool) f at h
      change bitKey variableID f = .dropped
      simp only [bitKey, ite_eq_left h]

theorem keyFields_eq_dropped_of_unused [DecidableEq I]
    (slots : I → MixedSupport.Slot) (f : MixedSupport.Assignment slots → Y)
    (h : ∀ i, Unused (MixedSupport.sectionFunction slots f i)) :
    MixedSupport.keyFields slots f = fun _ => .dropped := by
  funext i
  exact localKey_eq_dropped_of_unused (slots i)
    (MixedSupport.sectionFunction slots f i) (h i)

theorem keyFields_eq_dropped_of_constant [DecidableEq I]
    (slots : I → MixedSupport.Slot) (f : MixedSupport.Assignment slots → Y)
    (h : ∀ x x', f x = f x') :
    MixedSupport.keyFields slots f = fun _ => .dropped := by
  apply keyFields_eq_dropped_of_unused slots f
  intro i context u v
  exact h _ _

def retainedFields {n : Nat} (keys : Fin n → SlotKey) : List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, keys i))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

theorem retainedKeys_eq_retainedFields {n : Nat} (slots : Fin n → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Y) :
    MixedSupport.retainedKeys slots f = retainedFields (MixedSupport.keyFields slots f) := rfl

theorem mem_retainedFields {n : Nat} (keys : Fin n → SlotKey) (i : Fin n)
    (key : SlotKey) :
    (i, key) ∈ retainedFields keys ↔ key = keys i ∧ key ≠ .dropped := by
  constructor
  · intro h
    obtain ⟨hm, hretained⟩ := List.mem_filter.mp h
    obtain ⟨j, _, hpair⟩ := List.mem_map.mp hm
    have hji : j = i := congrArg Prod.fst hpair
    subst j
    have hkey : keys i = key := congrArg Prod.snd hpair
    exact ⟨hkey.symm, of_decide_eq_true hretained⟩
  · rintro ⟨rfl, hretained⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨i, ?_, rfl⟩, ?_⟩
    · simp
    · exact decide_eq_true hretained

def lookupField [DecidableEq I] (fields : List (I × SlotKey)) (i : I) : SlotKey :=
  match fields with
  | [] => .dropped
  | (j, key) :: rest => if i = j then key else lookupField rest i

theorem lookupField_eq_of_mem [DecidableEq I] (fields : List (I × SlotKey))
    (i : I) (key : SlotKey) :
    (i, key) ∈ fields → (∀ key', (i, key') ∈ fields → key' = key) →
      lookupField fields i = key := by
  induction fields with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨j, k⟩
      intro hmem hunique
      by_cases hij : i = j
      · subst i
        simp only [lookupField]
        exact hunique k (by simp)
      · simp only [lookupField, ite_eq_right hij]
        apply ih
        · apply (List.mem_cons.mp hmem).resolve_left
          intro hpair
          exact hij (congrArg Prod.fst hpair)
        · intro key' hkey'
          exact hunique key' (List.mem_cons_of_mem _ hkey')

theorem lookupField_eq_dropped [DecidableEq I] (fields : List (I × SlotKey)) (i : I) :
    (∀ key, (i, key) ∉ fields) → lookupField fields i = .dropped := by
  induction fields with
  | nil => intro _; rfl
  | cons head rest ih =>
      rcases head with ⟨j, k⟩
      intro hnone
      have hij : i ≠ j := by
        intro hij
        subst i
        exact hnone k (by simp)
      simp only [lookupField, ite_eq_right hij]
      apply ih
      intro key hkey
      exact hnone key (List.mem_cons_of_mem _ hkey)

theorem lookupField_retainedFields {n : Nat} (keys : Fin n → SlotKey) (i : Fin n) :
    lookupField (retainedFields keys) i = keys i := by
  by_cases hdropped : keys i = .dropped
  · calc
      lookupField (retainedFields keys) i = .dropped := by
        apply lookupField_eq_dropped
        intro key hkey
        obtain ⟨hkey, hretained⟩ := (mem_retainedFields keys i key).mp hkey
        exact hretained (hkey.trans hdropped)
      _ = keys i := hdropped.symm
  · apply lookupField_eq_of_mem
    · exact (mem_retainedFields keys i (keys i)).mpr ⟨rfl, hdropped⟩
    · intro key hkey
      exact ((mem_retainedFields keys i key).mp hkey).1

theorem retainedFields_injective {n : Nat} :
    Function.Injective (retainedFields (n := n)) := by
  intro keys keys' h
  funext i
  have hlookup := congrArg (fun fields => lookupField fields i) h
  simpa only [lookupField_retainedFields] using hlookup

theorem keyFields_eq_of_retainedKeys_eq {n : Nat}
    (slots projected : Fin n → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Y)
    (g : MixedSupport.Assignment projected → Z)
    (h : MixedSupport.retainedKeys slots f = MixedSupport.retainedKeys projected g) :
    MixedSupport.keyFields slots f = MixedSupport.keyFields projected g :=
  retainedFields_injective h

theorem legalAssignments_eq_of_retainedKeys_eq {n : Nat}
    (slots projected : Fin n → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Y)
    (g : MixedSupport.Assignment projected → Z)
    (h : MixedSupport.retainedKeys slots f = MixedSupport.retainedKeys projected g) :
    legalAssignments (MixedSupport.keyFields slots f) =
      legalAssignments (MixedSupport.keyFields projected g) :=
  congrArg legalAssignments (keyFields_eq_of_retainedKeys_eq slots projected f g h)

abbrev RetainedLocation (keys : I → SlotKey) := {i : I // keys i ≠ .dropped}

abbrev RetainedAssignment (keys : I → SlotKey) :=
  (i : RetainedLocation keys) → {value : ReducedValue // Allowed (keys i.val) value}

def restrictAssignment (keys : I → SlotKey) (values : ↥(legalAssignments keys)) :
    RetainedAssignment keys :=
  fun i => ⟨values.val i.val, values.property i.val⟩

noncomputable def extendAssignment (keys : I → SlotKey) (values : RetainedAssignment keys) :
    ↥(legalAssignments keys) := by
  classical
  refine ⟨fun i => if h : keys i = .dropped then .dropped else (values ⟨i, h⟩).val, ?_⟩
  change ∀ i, Allowed (keys i)
    (if h : keys i = .dropped then .dropped else (values ⟨i, h⟩).val)
  intro i
  by_cases h : keys i = .dropped
  · rw [dite_eq_left h, h]
    trivial
  · simpa only [dite_eq_right h] using (values ⟨i, h⟩).property

noncomputable def legalRetainedEquiv (keys : I → SlotKey) :
    ↥(legalAssignments keys) ≃ RetainedAssignment keys := by
  classical
  refine
    { toFun := restrictAssignment keys
      invFun := extendAssignment keys
      left_inv := ?_
      right_inv := ?_ }
  · intro values
    apply Subtype.ext
    funext i
    change (if h : keys i = .dropped then .dropped else values.val i) = values.val i
    by_cases h : keys i = .dropped
    · simp only [dite_eq_left h]
      have hv : Allowed .dropped (values.val i) := by
        simpa only [h] using values.property i
      exact ((allowed_dropped_iff _).mp hv).symm
    · simp only [dite_eq_right h]
  · intro values
    funext i
    apply Subtype.ext
    change (if h : keys i.val = .dropped then .dropped
      else (values ⟨i.val, h⟩).val) = (values i).val
    simp only [dite_eq_right i.property]

end PerfectCompleteness.DomainEncoding

end

end OAI
