import OAI.Computability.TypeSystem.Plain
import OAI.Computability.TypeSystem.Candidates

namespace OAI

/-! The actual candidate bases and the three kinds of observation values.
Plain indices retain their exact normalized expression tag. All coordinates
are candidates, rather than arbitrary sets of terms. -/
namespace PureTypeSystem
universe u

namespace PrimaryEdge
variable {S : Type u} {P : Specification S} {I J : Set S} {b : Bool}
theorem target_feasible (h : PrimaryEdge P I J b) : FeasibleProfile P J := by
  cases h with
  | inclusion _ h _ => exact h
  | domain h => exact h.product
  | codomain h => exact h.product
end PrimaryEdge

namespace ObservationLayers
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I : Set S}
theorem nonempty (h : I ∈ ObservationLayers P C) : I.Nonempty := by
  obtain ⟨s, hs, hn, hp⟩ := h
  cases hp with
  | refl => exact hn
  | tail _ he => exact he.target_feasible.1
end ObservationLayers

namespace ActiveLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I : Set S}
theorem nonempty (h : ActiveLayer P C I) : I.Nonempty := ObservationLayers.nonempty h.layer

theorem classify (h : ActiveLayer P C I) :
    PlainLayer P C I ∨ FreeLayer P C I false ∨ FreeLayer P C I true := by
  classical
  by_cases hp : PlainLayer P C I
  · exact .inl hp
  · obtain ⟨D, hd, b, hb⟩ := h
    cases b with
    | false => exact .inr (.inl ⟨hp, D, hd, hb⟩)
    | true => exact .inr (.inr ⟨hp, D, hd, hb⟩)
end ActiveLayer

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

abbrev Candidate (T : Expr S) := {A : Set (Expr S) // Candidates.IsCandidate Ω T A}
abbrev ActualType := {T : Expr S // Candidates.ActualType Ω T}
abbrev Base := (T : ActualType Ω) → Candidate Ω T.val

def topBase : Base Ω := fun T => ⟨Candidates.Top Ω T.val, Candidates.top_candidate⟩

/-- The exact coordinate update used at product syntax. -/
noncomputable def Base.update (b : Base Ω) (T : ActualType Ω) (A : Candidate Ω T.val) : Base Ω :=
  Function.update b T A

@[simp] theorem Base.update_same (b : Base Ω) (T : ActualType Ω) (A : Candidate Ω T.val) :
    Base.update Ω b T A T = A := by simp [Base.update]

@[simp] theorem Base.update_other (b : Base Ω) (T U : ActualType Ω) (A : Candidate Ω T.val)
    (h : U ≠ T) : Base.update Ω b T A U = b U := by simp [Base.update, h]

variable [Fintype S] (C : Set (Set S)) {hw : SystemWeaklyNormalizing P}
variable (hno : ¬ ForbiddenConfiguration P C)

abbrev PlainValue := (T : ActualPlain.Node Ω C) × ActualPlain.Space (hw := hw) hno (Base Ω) T
abbrev Plus := FreeObservations.Plus (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω) (Option (PlainValue (hw := hw) Ω C hno))
abbrev Minus := FreeObservations.Minus (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω) (Option (PlainValue (hw := hw) Ω C hno))

inductive RawValue : Type u
  | plain : PlainValue (hw := hw) Ω C hno → RawValue
  | plus : Plus (hw := hw) Ω C hno → RawValue
  | minus : Minus (hw := hw) Ω C hno → RawValue

/-- The tag and sign checks for an actual normalized type. -/
def Fits (T : Expr S) : RawValue (hw := hw) Ω C hno → Prop
  | .plain x => x.1.type = T
  | .plus _ => FreeLayer P C (Ω.profile T) false
  | .minus _ => FreeLayer P C (Ω.profile T) true

abbrev Value (T : Expr S) := {v : RawValue (hw := hw) Ω C hno // Fits (hw := hw) Ω C hno T v}

structure ActiveType where
  type : Expr S
  normal : Normal type
  sorted : ∃ s, Ω.HasType type (.sort s)
  active : ActiveLayer P C (Ω.profile type)

namespace ActiveType
variable {Ω C hno}
noncomputable abbrev ofActual (T : ActualType Ω) (ha : ActiveLayer P C (Ω.profile T.val)) :
    ActiveType Ω C where
  type := T.val
  normal := by rcases T.property with h | ⟨s, h⟩; exact h.1; exact h ▸ Normal.sort s
  sorted := by
    obtain ⟨s, hs⟩ := ha.nonempty
    have hn : Normal T.val := by
      rcases T.property with h | ⟨s, h⟩; exact h.1; exact h ▸ Normal.sort s
    exact ⟨s, by simpa only [ContextTower.profile, Set.mem_ofPred_eq,
      Expr.normalForm_of_normal hn] using hs⟩
  active := ha

def actual (T : ActiveType Ω C) : ActualType Ω := ⟨T.type, .inl ⟨T.normal, T.sorted⟩⟩
end ActiveType

noncomputable def plainDefault (T : ActualPlain.Node Ω C) : ActualPlain.Space (hw := hw) hno (Base Ω) T :=
  (ActualPlain.schema hw).distinguished (ActualPlain.dependency_wellFounded hno) (topBase Ω) T

noncomputable def distinguished (T : ActiveType Ω C) : Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.profile T.type)
  · let n : ActualPlain.Node Ω C := ⟨T.type, T.normal, T.sorted, hp⟩
    exact ⟨.plain ⟨n, plainDefault (hw := hw) Ω C hno n⟩, rfl⟩
  · by_cases hf : FreeLayer P C (Ω.profile T.type) false
    · exact ⟨.plus (FreeObservations.plusDefault _ _ (topBase Ω) none), hf⟩
    · have hm : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObservations.minusDefault _ _ (topBase Ω) none), hm⟩

noncomputable def RawValue.base : RawValue (hw := hw) Ω C hno → Base Ω
  | .plain p => (ActualPlain.prefixEquiv hno (Base Ω) p.1 p.2).1
  | .plus p => p.continuing []
  | .minus m => (FreeObservations.behavior _ _ _ _ m).continuing []

/-- Updating only the base keeps every nonempty observation unchanged. -/
noncomputable def withBase (T : ActiveType Ω C) (b : Base Ω) : Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.profile T.type)
  · let n : ActualPlain.Node Ω C := ⟨T.type, T.normal, T.sorted, hp⟩
    let e := ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n
    exact ⟨.plain ⟨n, e.symm (b, (e (plainDefault (hw := hw) Ω C hno n)).2)⟩, rfl⟩
  · by_cases hf : FreeLayer P C (Ω.profile T.type) false
    · exact ⟨.plus ⟨(fun s => if s = [] then b else topBase Ω), fun _ => none⟩, hf⟩
    · have hm : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObservations.embed _ _ _ _ 1
        ⟨(fun s => if s = [] then b else topBase Ω), fun _ => none⟩), hm⟩

theorem withBase_base (T : ActiveType Ω C) (b : Base Ω) :
    RawValue.base (hw := hw) Ω C hno (withBase (hw := hw) Ω C hno T b).val = b := by
  unfold withBase
  split
  · simp only [RawValue.base, Equiv.apply_symm_apply]
  · split
    · simp only [RawValue.base, ↓reduceIte]
    · simp only [RawValue.base, FreeObservations.behavior_embed, FreeObservations.stageBehavior,
        FreeObservations.Table.relabel, Function.comp_apply, FreeObservations.mapContinue,
        List.map_nil, ↓reduceIte]

/-- Invalid exit tags receive exactly the distinguished target. -/
noncomputable def project (T : ActiveType Ω C) (v : RawValue (hw := hw) Ω C hno) : Value (hw := hw) Ω C hno T.type :=
  if h : Fits (hw := hw) Ω C hno T.type v then ⟨v, h⟩ else distinguished (hw := hw) Ω C hno T

@[simp] theorem project_valid (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    project (hw := hw) Ω C hno T v.val = v := by
  simp only [project, v.property, dite_true, Subtype.coe_eta]

end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace RawValue

def LevelEq (n : Nat) : RawValue (hw := hw) Ω C hno → RawValue (hw := hw) Ω C hno → Prop
  | .plain p, .plain q => p = q
  | .plus p, .plus q => FreeObservations.Agree n p q
  | .minus p, .minus q => p = q
  | _, _ => False

def Bounded (n : Nat) : RawValue (hw := hw) Ω C hno → Prop
  | .minus p => FreeObservations.InStage n p
  | _ => True

variable {Ω C hno}
theorem level_refl (n : Nat) (v : RawValue (hw := hw) Ω C hno) : LevelEq _ _ _ n v v := by
  cases v <;> exact rfl

theorem level_mono {n m : Nat} (h : n ≤ m) {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq _ _ _ m v w) : LevelEq _ _ _ n v w := by
  cases v <;> cases w <;> try exact he
  exact FreeObservations.Agree.mono h he

theorem bounded_mono {n m : Nat} (h : n ≤ m) {v : RawValue (hw := hw) Ω C hno}
    (hv : Bounded _ _ _ n v) : Bounded _ _ _ m v := by
  cases v <;> try trivial
  exact FreeObservations.InStage.mono h hv

theorem exists_bound (v : RawValue (hw := hw) Ω C hno) : ∃ n, Bounded _ _ _ n v := by
  cases v with
  | plain p => exact ⟨0, trivial⟩
  | plus p => exact ⟨0, trivial⟩
  | minus p => exact FreeObservations.InStage.exists_stage p

theorem level_base {n : Nat} {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq _ _ _ n v w) : base _ _ _ v = base _ _ _ w := by
  cases v <;> cases w <;> try exact False.elim he
  · exact congrArg (fun p => (ActualPlain.prefixEquiv hno (Base Ω) p.1 p.2).1) he
  · exact congrFun (congrArg FreeObservations.Table.continuing he) []
  · exact congrArg (fun p => (FreeObservations.behavior _ _ _ _ p).continuing []) he
end RawValue
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u
namespace FreeLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}
theorem path_sign {s t b : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C J t)
    (e : SignedPath (SecondaryEdge P C) I J b) : s = Bool.xor b t := by
  obtain ⟨D, hd, hp⟩ := k.2
  exact h.sign_unique ⟨h.1, D, hd, e.append hp⟩
end FreeLayer

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (C : Set (Set S)) (hw : SystemWeaklyNormalizing P)

/-- A frame's key has the exact normalized domain and active target. -/
structure FrameKey (T : ActiveType Ω C) where
  domain : Expr S
  body : Expr S
  product : T.type = .pi domain body
  argument : Expr S
  normal : Normal argument
  typed : Ω.HasType argument domain
  active : ActiveLayer P C (Ω.profile (body.instantiate argument))

namespace FrameKey
variable {Ω C} {T : ActiveType Ω C} (a : FrameKey Ω C T)

theorem sorted : ∃ s, Ω.HasType (.pi a.domain a.body) (.sort s) :=
  a.product ▸ T.sorted

theorem domain_normal : Normal a.domain := (a.product ▸ T.normal).pi_domain

theorem body_normal : Normal a.body := (a.product ▸ T.normal).pi_body

theorem domain_sorted : ∃ s, Ω.HasType a.domain (.sort s) := by
  obtain ⟨s, hs⟩ := a.sorted
  exact Ω.domain_sorted hs

theorem target_sorted : ∃ s, Ω.HasType (a.body.instantiate a.argument) (.sort s) := by
  obtain ⟨s, hs⟩ := a.sorted
  exact Ω.frame_target_sorted hs a.typed

include hw

theorem profile_data : ∃ J,
    ProfileTriple P (Ω.profile a.domain) J (Ω.profile T.type) ∧
    PositivePath (PrimaryEdge P) (Ω.profile (a.body.instantiate a.argument)) J ∧
    ActiveLayer P C J := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hf, hp⟩ := Ω.frame_profiles hw hs a.typed
  rw [← a.product] at hf
  have hj := ObservationLayers.positive a.active.layer hp
  exact ⟨J, hf, hp, T.active.predecessor (.single (.positive hj T.active.layer (.codomain hf)))⟩

theorem target_path : PositivePath (SecondaryEdge P C)
    (Ω.profile (a.body.instantiate a.argument)) (Ω.profile T.type) := by
  obtain ⟨J, hf, hp, hj⟩ := a.profile_data hw
  exact .tail (ObservationLayers.secondary a.active.layer hp)
    (.positive hj.layer T.active.layer (.codomain hf))

theorem domain_active (hd : Ω.profile a.domain ∈ ObservationLayers P C) :
    ActiveLayer P C (Ω.profile a.domain) := by
  obtain ⟨J, hf, _, hj⟩ := a.profile_data hw
  exact T.active.predecessor (.single (.negative hd hj.layer T.active.layer hf))

theorem domain_edge (hd : ActiveLayer P C (Ω.profile a.domain)) :
    SecondaryEdge P C (Ω.profile a.domain) (Ω.profile T.type) true := by
  obtain ⟨J, hf, _, hj⟩ := a.profile_data hw
  exact .negative hd.layer hj.layer T.active.layer hf

noncomputable def target : ActiveType Ω C where
  type := (a.body.instantiate a.argument).normalForm
  normal := by
    obtain ⟨s, hs⟩ := a.target_sorted
    exact (Expr.normalForm_spec (hs.weaklyNormalizing hw)).2
  sorted := by
    obtain ⟨s, hs⟩ := a.target_sorted
    exact ⟨s, hs.normalForm hw⟩
  active := by simpa only [ContextTower.profile_normalForm] using a.active

def domainType (hd : ActiveLayer P C (Ω.profile a.domain)) : ActiveType Ω C :=
  ⟨a.domain, a.domain_normal, a.domain_sorted, hd⟩

theorem plain_target (hp : PlainLayer P C (Ω.profile T.type)) :
    PlainLayer P C (Ω.profile (a.target hw).type) := by
  simpa only [target, ContextTower.profile_normalForm] using hp.predecessor_path (a.target_path hw).reach

theorem plain_domain (hp : PlainLayer P C (Ω.profile T.type))
    (hd : ActiveLayer P C (Ω.profile a.domain)) : PlainLayer P C (Ω.profile a.domain) :=
  hp.predecessor (a.domain_edge hw hd)

theorem free_target_sign {s t : Bool}
    (hT : FreeLayer P C (Ω.profile T.type) s)
    (hL : FreeLayer P C (Ω.profile (a.target hw).type) t) : t = s := by
  have hl : FreeLayer P C (Ω.profile (a.body.instantiate a.argument)) t := by
    simpa only [target, ContextTower.profile_normalForm] using hL
  simpa using hl.path_sign hT (a.target_path hw).parity

theorem free_domain_sign {s t : Bool}
    (hT : FreeLayer P C (Ω.profile T.type) s)
    (hI : FreeLayer P C (Ω.profile a.domain) t) : t = !s := by
  have h := hI.edge_sign hT (a.domain_edge hw hI.active)
  simpa using h

/-- The third binder fact: quantified active payloads in a component's
product candidate are direct and hence can never be free minus. -/
theorem domain_direct (hC : IsComponent (PrimaryEdge P) C)
    (hK : Ω.profile T.type ∈ C) (hL : Ω.profile (a.target hw).type ∈ C)
    (hd : ActiveLayer P C (Ω.profile a.domain)) : DirectLayer P C (Ω.profile a.domain) := by
  obtain ⟨J, hf, hp, _⟩ := a.profile_data hw
  have hl : Ω.profile (a.body.instantiate a.argument) ∈ C := by
    simpa only [target, ContextTower.profile_normalForm] using hL
  have hj : J ∈ C := hC.between hl hK hp.reach (.single (.codomain hf))
  exact ⟨hd.layer, J, hj, Ω.profile T.type, hK, hf⟩

theorem domain_not_minus (hC : IsComponent (PrimaryEdge P) C)
    (hK : Ω.profile T.type ∈ C) (hL : Ω.profile (a.target hw).type ∈ C) :
    ¬ FreeLayer P C (Ω.profile a.domain) true := by
  intro hm
  exact Bool.noConfusion (hm.direct_sign (a.domain_direct hw hC hK hL hm.active))
end FrameKey

variable [Fintype S] {hw} (hno : ¬ ForbiddenConfiguration P C)

/-- Absence is mandatory at inactive domains. There are no latent values. -/
def PayloadFits (D : Expr S) (p : Option (RawValue (hw := hw) Ω C hno)) : Prop :=
  match p with
  | none => ¬ ActiveLayer P C (Ω.profile D)
  | some v => Fits Ω C hno D v

namespace Fits
variable {Ω C hno} {T : Expr S} {v : RawValue (hw := hw) Ω C hno}
theorem active (h : Fits Ω C hno T v) : ActiveLayer P C (Ω.profile T) := by
  cases v with
  | plain p => exact h ▸ p.1.plain.active
  | plus p => exact h.active
  | minus p => exact h.active
end Fits

abbrev PlusFrame := FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno)
  (Minus (hw := hw) Ω C hno)
abbrev MinusFrame := FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno)
  (Plus (hw := hw) Ω C hno)

def plusPayload : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno)
    (Minus (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .opposite m => some (.minus m)
  | .plain p => some (.plain p)

def minusPayload : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno)
    (Plus (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .opposite p => some (.plus p)
  | .plain p => some (.plain p)

/-- Exact gates for continue/exit operations at free lambdas. -/
def Gate (T : ActiveType Ω C) (q : Expr S)
    (p : Option (RawValue (hw := hw) Ω C hno)) (exit : Bool) : Prop :=
  ∃ a : FrameKey Ω C T, a.argument = q ∧ PayloadFits Ω C hno a.domain p ∧
    (PlainLayer P C (Ω.profile (a.target hw).type) ↔ exit = true)

end ObservationValues

namespace Converts
variable {S : Type u}
theorem app {f f' a a' : Expr S} (hf : Converts f f') (ha : Converts a a') :
    Converts (.app f a) (.app f' a') := by
  obtain ⟨g, hg, hg'⟩ := hf.join
  obtain ⟨b, hb, hb'⟩ := ha.join
  exact .trans _ _ _ (hg.app hb).converts (.symm _ _ (hg'.app hb').converts)

theorem lam {A A' b b' : Expr S} (hA : Converts A A') (hb : Converts b b') :
    Converts (.lam A b) (.lam A' b') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨c, hc, hc'⟩ := hb.join
  exact .trans _ _ _ (hD.lam hc).converts (.symm _ _ (hD'.lam hc').converts)
end Converts

namespace Expr.Scoped
variable {S : Type u} {n : Nat} {M : Expr S}
theorem subst_converts (hM : Scoped n M) {σ τ : Nat → Expr S}
    (hc : ∀ i, i < n → Converts (σ i) (τ i)) : Converts (M.subst σ) (M.subst τ) := by
  induction M generalizing n σ τ with
  | var i => exact hc i hM
  | sort s => exact .refl _
  | app f a ihf iha => exact .app (ihf hM.1 hc) (iha hM.2 hc)
  | lam A b ihA ihb | pi A b ihA ihb =>
    have he : ∀ i, i < n+1 → Converts (Expr.liftSub σ i) (Expr.liftSub τ i) := by
      intro i hi
      cases i with
      | zero => exact .refl _
      | succ i => exact (hc i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
    first
    | exact .lam (ihA hM.1 hc) (ihb hM.2 he)
    | exact .pi (ihA hM.1 hc) (ihb hM.2 he)
end Expr.Scoped

namespace Lookup
variable {S : Type u} {Γ : List (Expr S)} {n : Nat}
theorem exists_of_lt (hn : n < Γ.length) : ∃ A, Lookup Γ n A := by
  induction Γ generalizing n with
  | nil => exact False.elim (Nat.not_lt_zero _ hn)
  | cons A Γ ih =>
    cases n with
    | zero => exact ⟨_, .zero A Γ⟩
    | succ n =>
      obtain ⟨B, hb⟩ := ih (Nat.lt_of_succ_lt_succ hn)
      exact ⟨_, .succ A hb⟩

theorem unique {A B : Expr S} (hA : Lookup Γ n A) (hB : Lookup Γ n B) : A = B := by
  induction hA generalizing B with
  | zero => cases hB; rfl
  | succ A h ih => cases hB with
    | succ _ hB => exact congrArg (Expr.rename Nat.succ) (ih hB)
end Lookup

namespace ContextTower.HasType
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {M A : Expr S}

theorem actual_type (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Candidates.ActualType Ω A.normalForm := by
  rcases h.regularity with ⟨s, rfl⟩ | ⟨s, hs⟩
  · exact .inr ⟨s, Expr.normalForm_of_normal (Normal.sort s)⟩
  · exact .inl ⟨(Expr.normalForm_spec (hs.weaklyNormalizing hw)).2, s, hs.normalForm hw⟩

theorem actual_expression {s : S} (h : Ω.HasType M (.sort s)) (hw : SystemWeaklyNormalizing P) :
    Candidates.ActualType Ω M.normalForm :=
  .inl ⟨(Expr.normalForm_spec (h.weaklyNormalizing hw)).2, s, h.normalForm hw⟩
end ContextTower.HasType

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Parameter

def Bounded (n : Nat) (p : Option (RawValue (hw := hw) Ω C hno)) : Prop :=
  ∀ v, p = some v → RawValue.Bounded Ω C hno n v

def LevelEq (n : Nat) : Option (RawValue (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno) → Prop
  | none, none => True
  | some v, some w => RawValue.LevelEq Ω C hno n v w
  | _, _ => False

variable {Ω C hno}
theorem level_refl (n : Nat) (p : Option (RawValue (hw := hw) Ω C hno)) : LevelEq _ _ _ n p p := by
  cases p with
  | none => trivial
  | some p => exact p.level_refl n

theorem level_mono {n m : Nat} (h : n ≤ m) {p q : Option (RawValue (hw := hw) Ω C hno)}
    (he : LevelEq _ _ _ m p q) : LevelEq _ _ _ n p q := by
  cases p <;> cases q <;> try exact he
  exact RawValue.level_mono h he

theorem bounded_mono {n m : Nat} (h : n ≤ m) {p : Option (RawValue (hw := hw) Ω C hno)}
    (he : Bounded _ _ _ n p) : Bounded _ _ _ m p := fun v hv => RawValue.bounded_mono h (he v hv)

theorem exists_bound (p : Option (RawValue (hw := hw) Ω C hno)) : ∃ n, Bounded _ _ _ n p := by
  cases p with
  | none => exact ⟨0, fun _ h => by cases h⟩
  | some p =>
    obtain ⟨n, hn⟩ := p.exists_bound
    exact ⟨n, fun _ h => Option.some.inj h ▸ hn⟩
end Parameter

/-- Typed raw substitutions with precisely one observation parameter per
active actual declaration and none at inactive declarations. -/
structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TypedSubstitution Γ images
  parameters : Nat → Option (RawValue (hw := hw) Ω C hno)
  lawful : ∀ n A, Lookup Γ n A → PayloadFits Ω C hno (A.subst images).normalForm (parameters n)

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)} (e : Environment (hw := hw) Ω C hno Γ)

def Bounded (k : Nat) : Prop := ∀ n, n < Γ.length → Parameter.Bounded Ω C hno k (e.parameters n)

def ImageCompatible (f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  ∀ n, n < Γ.length → Converts (e.images n) (f.images n)

def LevelEq (k : Nat) (f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  ImageCompatible e f ∧ ∀ n, n < Γ.length → Parameter.LevelEq Ω C hno k (e.parameters n) (f.parameters n)

theorem bounded_mono {k l : Nat} (hkl : k ≤ l) (he : e.Bounded k) : e.Bounded l :=
  fun n hn => Parameter.bounded_mono hkl (he n hn)

theorem exists_bound : ∃ k, e.Bounded k := by
  have hh : ∀ n, ∃ k, ∀ i, i < n → Parameter.Bounded Ω C hno k (e.parameters i) := by
    intro n
    induction n with
    | zero => exact ⟨0, fun _ h => by omega⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨l, hl⟩ := Parameter.exists_bound (e.parameters n)
      refine ⟨max k l, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Parameter.bounded_mono (le_max_left k l) (hk i hi)
      · exact Parameter.bounded_mono (le_max_right k l) hl
  exact hh Γ.length

theorem level_refl (k : Nat) : e.LevelEq k e :=
  ⟨fun _ _ => .refl _, fun _ _ => Parameter.level_refl _ _⟩

theorem level_mono {k l : Nat} {f : Environment (hw := hw) Ω C hno Γ}
    (hkl : k ≤ l) (he : e.LevelEq l f) : e.LevelEq k f :=
  ⟨he.1, fun n hn => Parameter.level_mono hkl (he.2 n hn)⟩

/-- Binding a raw actual term does not normalize or evaluate its syntax. -/
def cons {A a : Expr S} (ha : Ω.HasType a (A.subst e.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p) :
    Environment (hw := hw) Ω C hno (A :: Γ) where
  images := fun n => match n with | 0 => a | n+1 => e.images n
  typed := e.typed.cons ha
  parameters := fun n => match n with | 0 => p | n+1 => e.parameters n
  lawful := by
    intro n B hn
    cases hn with
    | zero => simpa only [Expr.subst_rename, Function.comp_def] using hp
    | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using e.lawful _ _ hn

theorem bounded_cons {A a : Expr S} (ha : Ω.HasType a (A.subst e.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    {k : Nat} (he : e.Bounded k) (hb : Parameter.Bounded Ω C hno k p) :
    (e.cons ha p hp).Bounded k := by
  intro n hn
  cases n with
  | zero => exact hb
  | succ n => exact he n (Nat.lt_of_succ_lt_succ hn)

theorem actual_expr_eq {f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f)
    {M A : Expr S} (ht : HasType P Γ M A) :
    (M.subst e.images).normalForm = (M.subst f.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst ht e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst ht f.typed).weaklyNormalizing hw)
    (ht.scope.1.subst_converts he)

theorem actual_type_eq {f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f)
    {M A : Expr S} (ht : HasType P Γ M A) :
    (A.subst e.images).normalForm = (A.subst f.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst ht e.typed).type_weaklyNormalizing hw)
    ((ContextTower.HasType.subst ht f.typed).type_weaklyNormalizing hw)
    (ht.scope.2.subst_converts he)
end Environment
end ObservationValues

namespace WeaklyNormalizing
variable {S : Type u} {A B : Expr S}
theorem pi_domain (h : WeaklyNormalizing (.pi A B)) : WeaklyNormalizing A := by
  obtain ⟨N,hr,hn⟩ := h
  obtain ⟨D,E,rfl,hD,_⟩ := Reduces.pi_inv hr
  exact ⟨D,hD,hn.pi_domain⟩
theorem pi_body (h : WeaklyNormalizing (.pi A B)) : WeaklyNormalizing B := by
  obtain ⟨N,hr,hn⟩ := h
  obtain ⟨D,E,rfl,_,hE⟩ := Reduces.pi_inv hr
  exact ⟨E,hE,hn.pi_body⟩
end WeaklyNormalizing

namespace Expr
variable {S : Type u}
theorem instantiate_liftSub (E : Expr S) (σ : Nat → Expr S) (n : Expr S) :
    (E.subst (liftSub σ)).instantiate n =
      E.subst (fun i => match i with | 0 => n | i+1 => σ i) := by
  rw [instantiate, subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => simpa only [liftSub_succ, subst_rename, Function.comp_def, single] using subst_var (σ i)
end Expr

namespace ContextTower.HasType
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {M A : Expr S} {s : S}
theorem denormalize_type (h : Ω.HasType M A.normalForm) (hA : Ω.HasType A (.sort s))
    (hw : SystemWeaklyNormalizing P) : Ω.HasType M A :=
  h.conversion hA (.symm _ _ (Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts)
end ContextTower.HasType

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace PayloadFits
variable {Ω C hno}
theorem exists_of_actual (T : ActualType Ω) : ∃ p, PayloadFits (hw := hw) Ω C hno T.val p := by
  by_cases ha : ActiveLayer P C (Ω.profile T.val)
  · exact ⟨some (distinguished (hw := hw) Ω C hno (.ofActual T ha)).val,
      (distinguished (hw := hw) Ω C hno (.ofActual T ha)).property⟩
  · exact ⟨none,ha⟩
end PayloadFits

/-- A product's exact stored formation data and its raw environment. -/
structure ProductInstance where
  context : List (Expr S)
  domain : Expr S
  body : Expr S
  domainSort : S
  bodySort : S
  resultSort : S
  domainTyping : HasType P context domain (.sort domainSort)
  bodyTyping : HasType P (domain :: context) body (.sort bodySort)
  rule : P.rule domainSort bodySort resultSort
  environment : Environment (hw := hw) Ω C hno context

namespace ProductInstance
variable {Ω C hno} (t : ProductInstance (hw := hw) Ω C hno)
def rawDomain : Expr S := t.domain.subst t.environment.images
def rawBody : Expr S := t.body.subst (Expr.liftSub t.environment.images)
noncomputable def domainNF : Expr S := t.rawDomain.normalForm
noncomputable def bodyNF : Expr S := t.rawBody.normalForm
def rawTarget (n : Expr S) : Expr S :=
  t.body.subst (fun i => match i with | 0 => n | i+1 => t.environment.images i)
noncomputable def targetNF (n : Expr S) : Expr S := (t.rawTarget n).normalForm

theorem rawDomain_typed : Ω.HasType t.rawDomain (.sort t.domainSort) :=
  ContextTower.HasType.subst t.domainTyping t.environment.typed

theorem rawProduct_typed : Ω.HasType (.pi t.rawDomain t.rawBody) (.sort t.resultSort) :=
  ContextTower.HasType.subst (HasType.product t.domainTyping t.bodyTyping t.rule) t.environment.typed

theorem domain_typed : Ω.HasType t.domainNF (.sort t.domainSort) := t.rawDomain_typed.normalForm hw

theorem domain_normal : Normal t.domainNF := (Expr.normalForm_spec (t.rawDomain_typed.weaklyNormalizing hw)).2

theorem body_normal : Normal t.bodyNF :=
  (Expr.normalForm_spec (t.rawProduct_typed.weaklyNormalizing hw).pi_body).2

theorem product_nf : (Expr.pi t.rawDomain t.rawBody).normalForm = .pi t.domainNF t.bodyNF :=
  Expr.normalForm_pi (t.rawProduct_typed.weaklyNormalizing hw).pi_domain
    (t.rawProduct_typed.weaklyNormalizing hw).pi_body

theorem product_typed : Ω.HasType (.pi t.domainNF t.bodyNF) (.sort t.resultSort) := by
  rw [← t.product_nf]
  exact t.rawProduct_typed.normalForm hw

theorem rawArgument {n : Expr S} (hn : Ω.HasType n t.domainNF) : Ω.HasType n t.rawDomain :=
  hn.denormalize_type t.rawDomain_typed hw

noncomputable def extend {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno t.domainNF p) :
    Environment (hw := hw) Ω C hno (t.domain :: t.context) :=
  t.environment.cons (t.rawArgument hn) p hp

theorem rawTarget_typed {n : Expr S} (hn : Ω.HasType n t.domainNF) :
    Ω.HasType (t.rawTarget n) (.sort t.bodySort) :=
  ContextTower.HasType.subst t.bodyTyping (t.environment.typed.cons (t.rawArgument hn))

theorem target_typed {n : Expr S} (hn : Ω.HasType n t.domainNF) :
    Ω.HasType (t.targetNF n) (.sort t.bodySort) := (t.rawTarget_typed hn).normalForm hw

theorem target_normal {n : Expr S} (hn : Ω.HasType n t.domainNF) : Normal (t.targetNF n) :=
  (Expr.normalForm_spec ((t.rawTarget_typed hn).weaklyNormalizing hw)).2

theorem target_eq {n : Expr S} (hn : Ω.HasType n t.domainNF) :
    t.targetNF n = (t.bodyNF.instantiate n).normalForm := by
  have hr : Reduces (t.rawTarget n) (t.bodyNF.instantiate n) := by
    rw [rawTarget, ← Expr.instantiate_liftSub]
    exact (Expr.normalForm_spec (t.rawProduct_typed.weaklyNormalizing hw).pi_body).1.subst (Expr.single n)
  obtain ⟨s,hs⟩ := Ω.frame_target_sorted t.product_typed hn
  exact Expr.normalForm_converts ((t.rawTarget_typed hn).weaklyNormalizing hw)
    (hs.weaklyNormalizing hw) hr.converts

/-- The tester set uses the domain Read precisely at this primary component. -/
noncomputable def testers (d : Candidate Ω t.domainNF) : Set (Expr S) :=
  if Ω.profile t.domainNF ∈ C then d.val else Candidates.Top Ω t.domainNF

theorem testers_top (d : Candidate Ω t.domainNF) : t.testers d ⊆ Candidates.Top Ω t.domainNF := by
  unfold testers
  split
  · exact d.property.upper
  · exact Set.Subset.rfl

/-- Every raw tester and every matching payload has its own body Read.
This quantification is over all payloads, not only semantic realizers. -/
abbrev BodyReads := ∀ (n : Expr S), Ω.HasType n t.domainNF →
  (p : Option (RawValue (hw := hw) Ω C hno)) → PayloadFits Ω C hno t.domainNF p → Candidate Ω (t.targetNF n)

noncomputable def fibers (b : t.BodyReads) (n : Expr S) : Set (Set (Expr S)) :=
  if hn : Ω.HasType n t.domainNF then
    if Ω.profile (t.targetNF n) ∈ C then
      {U | ∃ p hp, U = (b n hn p hp).val}
    else {Candidates.Top Ω (t.targetNF n)}
  else ∅

theorem fibers_candidate (d : Candidate Ω t.domainNF) (b : t.BodyReads)
    {n : Expr S} (hn : n ∈ t.testers d) {U : Set (Expr S)} (hU : U ∈ t.fibers b n) :
    Candidates.IsCandidate Ω (t.bodyNF.instantiate n).normalForm U := by
  have ht := (t.testers_top d hn).1
  rw [← t.target_eq ht]
  simp only [fibers, ht, dite_true] at hU
  split_ifs at hU with hc
  · obtain ⟨p,hp,rfl⟩ := hU
    exact (b n ht p hp).property
  · have he : U = Candidates.Top Ω (t.targetNF n) := hU
    rw [he]
    exact Candidates.top_candidate

noncomputable def candidate (d : Candidate Ω t.domainNF) (b : t.BodyReads) :
    Candidate Ω (.pi t.domainNF t.bodyNF) :=
  ⟨Candidates.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b),
    Candidates.productTest_candidate hw (t.testers_top d) (fun _ hn _ hU => t.fibers_candidate d b hn hU)⟩

theorem candidate_top (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M : Expr S}
    (hM : M ∈ (t.candidate d b).val) : M ∈ Candidates.Top Ω (.pi t.domainNF t.bodyNF) := hM.1

theorem candidate_body (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M n : Expr S}
    (hM : M ∈ (t.candidate d b).val) (hn : n ∈ t.testers d)
    (hc : Ω.profile (t.targetNF n) ∈ C)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno t.domainNF p) :
    Expr.app M n ∈ (b n (t.testers_top d hn).1 p hp).val := by
  apply hM.2 n hn
  simp only [fibers, (t.testers_top d hn).1, dite_true, hc, ite_true, Set.mem_ofPred_eq]
  exact ⟨p,hp,rfl⟩

theorem candidate_outside (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M n : Expr S}
    (hM : M ∈ (t.candidate d b).val) (hn : n ∈ t.testers d)
    (hc : Ω.profile (t.targetNF n) ∉ C) :
    Expr.app M n ∈ Candidates.Top Ω (t.targetNF n) := by
  apply hM.2 n hn
  simp only [fibers, (t.testers_top d hn).1, dite_true, hc, ite_false, Set.mem_singleton_iff]
end ProductInstance
end ObservationValues
end PureTypeSystem

end OAI
