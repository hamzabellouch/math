import OAI.Computability.TypeSystem.Spaces
import OAI.Computability.TypeSystem.Potential

namespace OAI

/-! Actual plain observation spaces: the domain-feedback relation is well
founded for the source PTS syntax and exact source graph exclusion. -/
namespace PureTypeSystem
universe u
namespace ActualPlain
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (C : Set (Set S))

structure Node where
  type : Expr S
  normal : Normal type
  sorted : ∃ s, Ω.HasType type (.sort s)
  plain : PlainLayer P C (Ω.profile type)

structure Key (T : Node Ω C) where
  domain : Expr S
  body : Expr S
  product : T.type = .pi domain body
  argument : Expr S
  normal : Normal argument
  typed : Ω.HasType argument domain
  active : ActiveLayer P C (Ω.profile (body.instantiate argument))

variable {Ω C}
variable (hw : SystemWeaklyNormalizing P)

namespace Key
variable {T : Node Ω C} (a : Key Ω C T)

theorem sorted : ∃ s, Ω.HasType (.pi a.domain a.body) (.sort s) := by
  simpa only [← a.product] using T.sorted

include hw

theorem target_reach : Reach (SecondaryEdge P C)
    (Ω.profile (a.body.instantiate a.argument)) (Ω.profile T.type) := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hj, hp⟩ := Ω.frame_profiles hw hs a.typed
  have hJ := ObservationLayers.positive a.active.layer hp
  exact (ObservationLayers.secondary a.active.layer hp).reach.trans (.single (.positive hJ T.plain.active.layer
    (a.product ▸ PrimaryEdge.codomain hj)))

theorem open_active : ∃ J, ProfileTriple P (Ω.profile a.domain) J (Ω.profile T.type) ∧
    ActiveLayer P C J := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hj, hp⟩ := Ω.frame_profiles hw hs a.typed
  have hJ := ObservationLayers.positive a.active.layer hp
  have he : SecondaryEdge P C J (Ω.profile T.type) false :=
    .positive hJ T.plain.active.layer (a.product ▸ PrimaryEdge.codomain hj)
  exact ⟨J, a.product ▸ hj, T.plain.active.predecessor (.single he)⟩

theorem domain_edge (ha : ActiveLayer P C (Ω.profile a.domain)) :
    SecondaryEdge P C (Ω.profile a.domain) (Ω.profile T.type) true := by
  obtain ⟨J, hj, hJ⟩ := a.open_active hw
  exact .negative ha.layer hJ.layer T.plain.active.layer hj

noncomputable def target : Node Ω C where
  type := (a.body.instantiate a.argument).normalForm
  normal := by
    obtain ⟨s, hs⟩ := a.sorted
    obtain ⟨b, hb⟩ := Ω.frame_target_sorted hs a.typed
    exact (Expr.normalForm_spec (hb.weaklyNormalizing hw)).2
  sorted := by
    obtain ⟨s, hs⟩ := a.sorted
    obtain ⟨b, hb⟩ := Ω.frame_target_sorted hs a.typed
    exact ⟨b, hb.normalForm hw⟩
  plain := by
    rw [Ω.profile_normalForm]
    exact T.plain.predecessor_path (a.target_reach hw)

noncomputable def domainNode (ha : ActiveLayer P C (Ω.profile a.domain)) : Node Ω C where
  type := a.domain
  normal := by
    have hh := T.normal
    rw [a.product] at hh
    exact hh.pi_domain
  sorted := by
    obtain ⟨s, hs⟩ := a.sorted
    exact Ω.domain_sorted hs
  plain := T.plain.predecessor (a.domain_edge hw ha)

@[simp] theorem target_profile : Ω.profile (a.target hw).type =
    Ω.profile (a.body.instantiate a.argument) := Ω.profile_normalForm _

@[simp] theorem domainNode_type (ha : ActiveLayer P C (Ω.profile a.domain)) :
    (a.domainNode hw ha).type = a.domain := rfl
end Key

noncomputable def schema : PlainSpaces.Schema (Node Ω C) where
  Key := Key Ω C
  target := fun _ a => a.target hw
  domain := fun _ a => if ha : ActiveLayer P C (Ω.profile a.domain)
    then some (a.domainNode hw ha) else none

variable {hw}

namespace Schema

theorem target_reach {n : Node Ω C} (a : (schema hw).Key n) :
    Reach (SecondaryEdge P C) (Ω.profile ((schema hw).target n a).type) (Ω.profile n.type) := by
  simpa only [schema, Key.target, ContextTower.profile_normalForm] using a.target_reach hw

theorem domain_eq {n d : Node Ω C} {a : (schema hw).Key n}
    (he : (schema hw).domain n a = some d) :
    ∃ ha : ActiveLayer P C (Ω.profile a.domain), d = a.domainNode hw ha := by
  change (if ha : ActiveLayer P C (Ω.profile a.domain) then some (a.domainNode hw ha) else none) = some d at he
  split at he
  · rename_i ha
    exact ⟨ha, (Option.some.inj he).symm⟩
  · cases he

theorem dependency_path {n d : Node Ω C} (hd : (schema hw).Dependency d n) :
    ∃ I K, SecondaryEdge P C I K true ∧ Reach (SecondaryEdge P C) (Ω.profile d.type) I ∧
      Reach (SecondaryEdge P C) K (Ω.profile n.type) := by
  induction hd with
  | @head n a d he =>
    obtain ⟨ha, rfl⟩ := domain_eq he
    exact ⟨Ω.profile a.domain, Ω.profile n.type, a.domain_edge hw ha, .refl _, .refl _⟩
  | @tail n d a hd ih =>
    obtain ⟨I, K, he, hi, hk⟩ := ih
    exact ⟨I, K, he, hi, hk.trans (target_reach a)⟩

theorem dependency_reach {n d : Node Ω C} (hd : (schema hw).Dependency d n) :
    Reach (SecondaryEdge P C) (Ω.profile d.type) (Ω.profile n.type) := by
  obtain ⟨I, K, he, hi, hk⟩ := dependency_path hd
  exact hi.trans ((Reach.single he).trans hk)

theorem dependency_negative {n d : Node Ω C} (hd : (schema hw).Dependency d n)
    {D : Set (Set S)} (hD : IsComponent (SecondaryEdge P C) D)
    (hn : Ω.profile n.type ∈ D) (hd' : Ω.profile d.type ∈ D) :
    ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true := by
  obtain ⟨I, K, he, hi, hk⟩ := dependency_path hd
  exact ⟨I, hD.between hd' hn hi ((Reach.single he).trans hk), K,
    hD.between hd' hn (hi.trans (.single he)) hk, he⟩

variable (hw)

theorem dependency_drop (hno : ¬ ForbiddenConfiguration P C)
    {n d : Node Ω C} (hd : (schema hw).Dependency d n)
    {D : Set (Set S)} (hD : IsComponent (SecondaryEdge P C) D)
    (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hn : Ω.profile n.type ∈ D) (hd' : Ω.profile d.type ∈ D) :
    Ω.potential C D d.type < Ω.potential C D n.type := by
  induction hd with
  | @head n a d he =>
    obtain ⟨ha, rfl⟩ := domain_eq he
    obtain ⟨s, hs⟩ := a.sorted
    have hh := Ω.frame_domain_drop hw hs a.typed
      (a.product ▸ n.plain.active) a.active hd'
    simpa only [Key.domainNode, ← a.product] using hh
  | @tail n d a hd ih =>
    have htarget : Ω.profile ((schema hw).target n a).type ∈ D :=
      hD.between hd' hn (dependency_reach hd) (target_reach a)
    have hneg := dependency_negative hd hD htarget hd'
    have hh := ih htarget hd'
    obtain ⟨s, hs⟩ := a.sorted
    have hnN : Normal (.pi a.domain a.body) := a.product ▸ n.normal
    have hdrop := Ω.frame_target_drop hw hno hD hplain hneg hs hnN a.typed
      (a.product ▸ hn) (by simpa only [schema, Key.target, ContextTower.profile_normalForm] using htarget)
    exact hh.trans (by simpa only [schema, Key.target, ← a.product] using hdrop)

end Schema

variable [Fintype S]

noncomputable def measure (n : Node Ω C) : Nat × Nat :=
  (Reach.rank (SecondaryEdge P C) (Ω.profile n.type),
   Ω.potential C (Reach.component (SecondaryEdge P C) (Ω.profile n.type)) n.type)

/-- All domain feedback, including feedback reached after arbitrarily many
continuing frames, is strictly well founded. No bound on path length is used. -/
theorem dependency_wellFounded (hno : ¬ ForbiddenConfiguration P C) :
    WellFounded (schema (Ω := Ω) (C := C) hw).Dependency := by
  apply ((Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.onFun (f := measure (Ω := Ω) (C := C))).mono
  intro d n hd
  have hr := Schema.dependency_reach hd
  have hle := Reach.rank_mono (SecondaryEdge P C) hr
  change Prod.Lex (· < ·) (· < ·)
    (Reach.rank (SecondaryEdge P C) (Ω.profile d.type),
      Ω.potential C (Reach.component (SecondaryEdge P C) (Ω.profile d.type)) d.type)
    (Reach.rank (SecondaryEdge P C) (Ω.profile n.type),
      Ω.potential C (Reach.component (SecondaryEdge P C) (Ω.profile n.type)) n.type)
  rcases lt_or_eq_of_le hle with hlt | he
  · exact .left _ _ hlt
  · have hc := Reach.component_eq_of_rank_eq (SecondaryEdge P C) hr he
    have hdn : Ω.profile d.type ∈ Reach.component (SecondaryEdge P C) (Ω.profile n.type) :=
      ⟨Reach.reverse_of_rank_eq (SecondaryEdge P C) hr he, hr⟩
    have hdrop := Schema.dependency_drop hw hno hd
      (Reach.component_isComponent (SecondaryEdge P C) (Ω.profile n.type))
      n.plain.component_plain (Reach.mem_component _ _) hdn
    rw [he, hc]
    exact .right _ hdrop

/-- The actual (not postulated) plain observation space of every normalized
plain actual type. The base parameter B is the set of candidate assignments
when used by the component interpretation. -/
noncomputable def Space (hno : ¬ ForbiddenConfiguration P C) (B : Type u)
    (n : Node Ω C) : Type u :=
  (schema hw).Space (dependency_wellFounded hno) B n

noncomputable def prefixEquiv (hno : ¬ ForbiddenConfiguration P C) (B : Type u)
    (n : Node Ω C) : Space (hw := hw) hno B n ≃
      B × ((a : (schema hw).Key n) →
        (schema hw).FrameParameters (Space (hw := hw) hno B) a →
        Space (hw := hw) hno B ((schema hw).target n a)) :=
  (schema hw).prefixEquiv (dependency_wellFounded hno) B n

end ActualPlain
end PureTypeSystem

end OAI
