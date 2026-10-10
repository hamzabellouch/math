import OAI.Computability.PerfectCompleteness.Foundations.ClauseSupportLemmas

namespace OAI

section

namespace PerfectCompleteness.ReducedDomains

open ClauseSupport

variable {I C Y : Type*}

def Allowed : SlotKey → ReducedValue → Prop
  | .dropped, .dropped => True
  | .bit _, .bit _ => True
  | .full _ signs, .full value => value ∈ SourceClause.satisfyingTriples signs
  | _, _ => False

theorem allowed_nonempty (key : SlotKey) : ∃ value, Allowed key value := by
  cases key with
  | dropped => exact ⟨.dropped, trivial⟩
  | bit variableID => exact ⟨.bit false, trivial⟩
  | full occurrence signs =>
      obtain ⟨u, _⟩ := ClauseSupport.coordinate_surjective signs 0 false
      exact ⟨.full u.val, u.property⟩

theorem localReduction_range_iff (s : MixedSupport.Slot)
    (f : C → s.Domain → Y) (value : ReducedValue) :
    (∃ u : s.Domain, MixedSupport.localReduction s f u = value) ↔
      Allowed (MixedSupport.localKey s f) value := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
      change (∃ u : Answer signs, clauseReduction f u = value) ↔
        Allowed (clauseKey occurrence variableIDs f) value
      cases hm : clauseMode f with
      | dropped =>
          cases value <;>
            simp [clauseReduction, clauseKey, hm, reduceByMode, Allowed]
      | bit position =>
          cases value with
          | dropped =>
              simp [clauseReduction, clauseKey, hm, reduceByMode, Allowed]
          | bit b =>
              simp only [clauseReduction, clauseKey, hm, reduceByMode, Allowed,
                ReducedValue.bit.injEq, iff_true]
              exact ClauseSupport.coordinate_surjective signs position b
          | full triple =>
              simp [clauseReduction, clauseKey, hm, reduceByMode, Allowed]
      | full =>
          cases value with
          | dropped =>
              simp [clauseReduction, clauseKey, hm, reduceByMode, Allowed]
          | bit b =>
              simp [clauseReduction, clauseKey, hm, reduceByMode, Allowed]
          | full triple =>
              simp only [clauseReduction, clauseKey, hm, reduceByMode, Allowed,
                ReducedValue.full.injEq]
              constructor
              · rintro ⟨u, rfl⟩
                exact u.property
              · intro htriple
                exact ⟨⟨triple, htriple⟩, rfl⟩
  | bit variableID =>
      change C → Bool → Y at f
      change (∃ b : Bool, bitReduction f b = value) ↔
        Allowed (bitKey variableID f) value
      by_cases hu : Unused f
      · cases value <;> simp [bitReduction, bitKey, hu, Allowed]
      · cases value <;> simp [bitReduction, bitKey, hu, Allowed]

theorem localReduction_allowed (s : MixedSupport.Slot)
    (f : C → s.Domain → Y) (u : s.Domain) :
    Allowed (MixedSupport.localKey s f) (MixedSupport.localReduction s f u) :=
  (localReduction_range_iff s f _).mp ⟨u, rfl⟩

def legalAssignments (keys : I → SlotKey) : Set (I → ReducedValue) :=
  {values | ∀ i, Allowed (keys i) (values i)}

theorem mem_legalAssignments (keys : I → SlotKey) (values : I → ReducedValue) :
    values ∈ legalAssignments keys ↔ ∀ i, Allowed (keys i) (values i) := Iff.rfl

theorem legalAssignments_nonempty (keys : I → SlotKey) :
    (legalAssignments keys).Nonempty := by
  classical
  choose values hvalues using fun i => allowed_nonempty (keys i)
  exact ⟨values, hvalues⟩

theorem range_reduction [DecidableEq I] (slots : I → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Y) :
    Set.range (MixedSupport.reduction slots f) =
      legalAssignments (MixedSupport.keyFields slots f) := by
  classical
  ext values
  change (∃ x, MixedSupport.reduction slots f x = values) ↔
    ∀ i, Allowed (MixedSupport.keyFields slots f i) (values i)
  constructor
  · rintro ⟨x, rfl⟩ i
    exact localReduction_allowed (slots i) (MixedSupport.sectionFunction slots f i) (x i)
  · intro hvalues
    have preimages : ∀ i, ∃ u : (slots i).Domain,
        MixedSupport.localReduction (slots i) (MixedSupport.sectionFunction slots f i) u =
          values i := by
      intro i
      exact (localReduction_range_iff (slots i)
        (MixedSupport.sectionFunction slots f i) (values i)).mpr (hvalues i)
    choose x hx using preimages
    refine ⟨x, ?_⟩
    funext i
    exact hx i

private def valueCode : ReducedValue → Option (Bool ⊕ SourceClause.Triple)
  | .dropped => none
  | .bit b => some (.inl b)
  | .full triple => some (.inr triple)

private theorem valueCode_injective : Function.Injective valueCode := by
  intro u v h
  cases u <;> cases v <;> simp_all [valueCode]

theorem reducedValue_finite : Finite ReducedValue :=
  Finite.of_injective valueCode valueCode_injective

theorem legalAssignments_finite [Finite I] (keys : I → SlotKey) :
    (legalAssignments keys).Finite := by
  let : Finite ReducedValue := reducedValue_finite
  exact Set.toFinite _

end PerfectCompleteness.ReducedDomains

end

end OAI
