import OAI.Computability.TypeSystem.Values
import OAI.Computability.TypeSystem.Interface

namespace OAI

/-! Total observation operations. The minus lambda pack is provisional off the
representable behaviors; the finite-bound theorem proves that the evaluator
never takes that provisional branch. -/
namespace PureTypeSystem
universe u

namespace ActualPlain.Node
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {C : Set (Set S)}
@[ext] theorem ext {n m : ActualPlain.Node Ω C} (h : n.type = m.type) : n = m := by
  cases n; cases m; cases h; rfl
end ActualPlain.Node

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace ActiveType
variable {Ω C}
abbrev plainNode (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type)) : ActualPlain.Node Ω C :=
  ⟨T.type, T.normal, T.sorted, hp⟩
omit [Fintype S] in
@[ext] theorem ext {T U : ActiveType Ω C} (h : T.type = U.type) : T = U := by
  cases T; cases U; cases h; rfl
end ActiveType

namespace Value
variable {Ω C hno}
def plain (n : ActualPlain.Node Ω C) (p : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    Value (hw := hw) Ω C hno n.type := ⟨.plain ⟨n,p⟩, rfl⟩

theorem plain_exists (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    ∃ p, plain n p = v := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p =>
    have he : p.1 = n := ActualPlain.Node.ext hv
    rcases p with ⟨m,p⟩
    dsimp at he
    subst m
    exact ⟨p,rfl⟩
  | plus p => exact False.elim (hv.1 n.plain)
  | minus p => exact False.elim (hv.1 n.plain)

noncomputable def asPlain (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    ActualPlain.Space (hw := hw) hno (Base Ω) n := (plain_exists n v).choose

@[simp] theorem plain_asPlain (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    plain n (asPlain n v) = v := (plain_exists n v).choose_spec

@[simp] theorem asPlain_plain (n : ActualPlain.Node Ω C) (p : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    asPlain n (plain n p) = p := by
  have he := congrArg Subtype.val (plain_asPlain n (plain n p))
  exact eq_of_heq (Sigma.mk.inj (RawValue.plain.inj he)).2

theorem plus_exists {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (v : Value (hw := hw) Ω C hno T) : ∃ p, v.val = .plus p := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact ⟨p,rfl⟩
  | minus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))

theorem minus_exists {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (v : Value (hw := hw) Ω C hno T) : ∃ p, v.val = .minus p := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))
  | minus p => exact ⟨p,rfl⟩

noncomputable def asPlus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (v : Value (hw := hw) Ω C hno T) : Plus (hw := hw) Ω C hno := (plus_exists hT v).choose
noncomputable def asMinus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (v : Value (hw := hw) Ω C hno T) : Minus (hw := hw) Ω C hno := (minus_exists hT v).choose

@[simp] theorem asPlus_spec {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (v : Value (hw := hw) Ω C hno T) : v.val = .plus (asPlus hT v) := (plus_exists hT v).choose_spec
@[simp] theorem asMinus_spec {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (v : Value (hw := hw) Ω C hno T) : v.val = .minus (asMinus hT v) := (minus_exists hT v).choose_spec
end Value

namespace ActualPlainKey
variable {Ω C hno}
def frame {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n) :
    FrameKey Ω C (⟨n.type,n.normal,n.sorted,n.plain.active⟩ : ActiveType Ω C) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩

/-- Decode a plain frame's unique optional domain coordinate. -/
noncomputable def payload {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    Option (RawValue (hw := hw) Ω C hno) :=
  if h : ActiveLayer P C (Ω.profile a.domain) then
    some (.plain ⟨a.domainNode hw h, p _ (by simp only [ActualPlain.schema, h, dite_true])⟩)
  else none

theorem payload_fits {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    PayloadFits Ω C hno a.domain (payload a p) := by
  unfold payload
  split
  · rfl
  · assumption

/-- Encode the matching typed plain payload without changing its tag. -/
noncomputable def parameters {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a := by
  cases p with
  | none =>
    intro d hd
    exact False.elim (hp (ActualPlain.Schema.domain_eq hd).choose)
  | some v =>
    intro d hd
    apply Value.asPlain d
    refine ⟨v,?_⟩
    obtain ⟨ha,rfl⟩ := ActualPlain.Schema.domain_eq hd
    exact hp

@[simp] theorem payload_parameters {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    payload a (parameters a p hp) = p := by
  unfold payload
  split
  · rename_i ha
    cases p with
    | none => exact False.elim (hp ha)
    | some v =>
      simpa only [parameters, Value.plain] using
        congrArg (fun w : Value (hw := hw) Ω C hno a.domain => some w.val)
          (Value.plain_asPlain (a.domainNode hw ha) ⟨v,hp⟩)
  · rename_i ha
    cases p with
    | none => rfl
    | some v => exact False.elim (ha hp.active)
theorem payload_injective {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n) :
    Function.Injective (payload (hw := hw) (hno := hno) a) := by
  intro p q he
  funext d hd
  obtain ⟨ha,rfl⟩ := ActualPlain.Schema.domain_eq hd
  simp only [payload, ha, dite_true, Option.some.injEq, RawValue.plain.injEq] at he
  exact eq_of_heq (Sigma.mk.inj he).2

@[simp] theorem parameters_payload {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    parameters a (payload a p) (payload_fits a p) = p :=
  payload_injective a (payload_parameters a (payload a p) (payload_fits a p))

end ActualPlainKey

namespace FrameKey
variable {Ω C hno}
omit [Fintype S] in
@[ext] theorem ext {T : ActiveType Ω C} {a b : FrameKey Ω C T}
    (h : a.argument = b.argument) : a = b := by
  cases a with
  | mk D E ht q hn hh hact =>
    cases b with
    | mk D' E' ht' q' hn' hh' hact' =>
      obtain ⟨rfl,rfl⟩ := Expr.pi.inj (ht.symm.trans ht')
      cases h
      rfl

abbrev plainKey {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hT : PlainLayer P C (Ω.profile T.type)) : ActualPlain.Key Ω C (T.plainNode hT) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩

omit [Fintype S] in
theorem free_target {T : ActiveType Ω C} (a : FrameKey Ω C T) {sgn : Bool}
    (hT : FreeLayer P C (Ω.profile T.type) sgn)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    FreeLayer P C (Ω.profile (a.target hw).type) sgn := by
  rcases (a.target hw).active.classify with h | h | h
  · exact False.elim (ht h)
  · exact a.free_target_sign hw hT h ▸ h
  · exact a.free_target_sign hw hT h ▸ h
end FrameKey

/-- A represented minus behavior is packed without changing any observation. -/
noncomputable def packMinus
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno)) : Minus (hw := hw) Ω C hno :=
  if h : ∃ x, FreeObservations.behavior _ _ _ _ x = t then h.choose
  else FreeObservations.minusDefault _ _ (topBase Ω) none

theorem packMinus_spec
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno))
    (h : ∃ x, FreeObservations.behavior _ _ _ _ x = t) :
    FreeObservations.behavior _ _ _ _ (packMinus Ω C hno t) = t := by
  simp only [packMinus, h, dite_true]
  exact h.choose_spec

theorem packMinus_stage {n : Nat}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno))
    (h : ∃ x, FreeObservations.InStage n x ∧ FreeObservations.behavior _ _ _ _ x = t) :
    FreeObservations.InStage n (packMinus Ω C hno t) := by
  obtain ⟨x,hx,he⟩ := h
  have hp := packMinus_spec Ω C hno t ⟨x,he⟩
  have hh := FreeObservations.behavior_injective (topBase Ω) (none : Option (PlainValue (hw := hw) Ω C hno))
    (hp.trans he.symm)
  exact hh ▸ hx
end ObservationValues
end PureTypeSystem


namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Gate
variable {Ω C hno} {T : ActiveType Ω C} {q : Expr S}
variable {p : Option (RawValue (hw := hw) Ω C hno)} {exit : Bool}
noncomputable def frame (h : Gate Ω C hno T q p exit) : FrameKey Ω C T := h.choose

theorem argument (h : Gate Ω C hno T q p exit) : h.frame.argument = q := h.choose_spec.1
theorem payload (h : Gate Ω C hno T q p exit) : PayloadFits Ω C hno h.frame.domain p := h.choose_spec.2.1

theorem plain (h : Gate Ω C hno T q p true) :
    PlainLayer P C (Ω.profile (h.frame.target hw).type) := h.choose_spec.2.2.mpr rfl

theorem not_plain (h : Gate Ω C hno T q p false) :
    ¬ PlainLayer P C (Ω.profile (h.frame.target hw).type) := fun hp => Bool.noConfusion (h.choose_spec.2.2.mp hp)

theorem unique (h : Gate Ω C hno T q p exit) (a : FrameKey Ω C T) (ha : a.argument = q) :
    h.frame = a := FrameKey.ext (h.argument.trans ha.symm)
end Gate

abbrev LambdaAction (T : ActiveType Ω C) := (a : FrameKey Ω C T) →
  (p : Option (RawValue (hw := hw) Ω C hno)) → PayloadFits Ω C hno a.domain p →
  Value (hw := hw) Ω C hno (a.target hw).type

noncomputable def tagPlain (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) : PlainValue (hw := hw) Ω C hno :=
  ⟨T.plainNode hp, Value.asPlain (T.plainNode hp) v⟩

theorem tagPlain_spec (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) : RawValue.plain (tagPlain Ω C hno T hp v) = v.val :=
  congrArg Subtype.val (Value.plain_asPlain (T.plainNode hp) v)

/-- The actual plain prefix operation, with the unique optional payload. -/
noncomputable def plainLambda (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    (act : LambdaAction (hw := hw) Ω C hno T) : Value (hw := hw) Ω C hno T.type := by
  let n := T.plainNode hp
  apply Value.plain n
  refine (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n).symm ⟨topBase Ω, fun a p => ?_⟩
  let a' : FrameKey Ω C T := ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
  exact Value.asPlain (a.target hw)
    (act a' (ActualPlainKey.payload a p) (ActualPlainKey.payload_fits a p))

/-- The same gate is used for plus and minus exits; the opposite payload
space differs, but the exact plain target tag is always retained. -/
noncomputable def lambdaExit {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X) :
    Option (PlainValue (hw := hw) Ω C hno) :=
  if h : Gate Ω C hno T a.1 (decode a.2) true then
    some (tagPlain Ω C hno (h.frame.target hw) h.plain (act h.frame (decode a.2) h.payload))
  else none

noncomputable def plusContinue (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : PlusFrame (hw := hw) Ω C hno) : Plus (hw := hw) Ω C hno :=
  if h : Gate Ω C hno T a.1 (plusPayload Ω C hno a.2) false then
    Value.asPlus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObservations.plusDefault _ _ (topBase Ω) none

noncomputable def minusContinue (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : MinusFrame (hw := hw) Ω C hno) : Minus (hw := hw) Ω C hno :=
  if h : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false then
    Value.asMinus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObservations.minusDefault _ _ (topBase Ω) none

noncomputable def plusLambda (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T) :
    Plus (hw := hw) Ω C hno where
  continuing
    | [] => topBase Ω
    | a :: as => (plusContinue Ω C hno T hT act a).continuing as
  exiting
    | ([], a) => lambdaExit Ω C hno (plusPayload Ω C hno) T act a
    | (a :: as, e) => (plusContinue Ω C hno T hT act a).exiting (as,e)

noncomputable def minusLambdaBehavior (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T) :=
  FreeObservations.lambdaTable (topBase Ω) (minusContinue Ω C hno T hT act)
    (lambdaExit Ω C hno (minusPayload Ω C hno) T act)

noncomputable def lambdaValue (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T) :
    Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.profile T.type)
  · exact plainLambda Ω C hno T hp act
  · by_cases hf : FreeLayer P C (Ω.profile T.type) false
    · exact ⟨.plus (plusLambda Ω C hno T hf act),hf⟩
    · have hm : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hm act)),hm⟩

namespace FrameKey
variable {Ω C hno} {T : ActiveType Ω C} (a : FrameKey Ω C T)

noncomputable def plusParameter (hT : FreeLayer P C (Ω.profile T.type) false)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Minus (hw := hw) Ω C hno) := by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | minus m => exact .opposite m
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

noncomputable def minusParameter (hT : FreeLayer P C (Ω.profile T.type) true)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Plus (hw := hw) Ω C hno) := by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | plus m => exact .opposite m
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

@[simp] theorem plusPayload_parameter (hT : FreeLayer P C (Ω.profile T.type) false)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    plusPayload Ω C hno (a.plusParameter hT p hp) = p := by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | minus m => rfl
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

@[simp] theorem minusPayload_parameter (hT : FreeLayer P C (Ω.profile T.type) true)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    minusPayload Ω C hno (a.minusParameter hT p hp) = p := by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | plus m => rfl
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
end FrameKey

noncomputable def exitValue (T : ActiveType Ω C) (out : Option (PlainValue (hw := hw) Ω C hno)) :
    Value (hw := hw) Ω C hno T.type :=
  match out with
  | none => distinguished (hw := hw) Ω C hno T
  | some p => project (hw := hw) Ω C hno T (.plain p)

/-- Plain application, separated to keep dependent prefix casts abstract. -/
noncomputable def plainApply (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    Value (hw := hw) Ω C hno (a.target hw).type := by
  let n := T.plainNode hT
  let a' := a.plainKey hT
  let ps := ActualPlainKey.parameters a' p hp
  exact Value.plain (a'.target hw)
    ((ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n (Value.asPlain n v)).2 a' ps)

/-- Exact application: plain next, free continue slice, or checked exit. -/
noncomputable def applyValue (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) : Value (hw := hw) Ω C hno (a.target hw).type := by
  by_cases hT : PlainLayer P C (Ω.profile T.type)
  · exact plainApply Ω C hno T hT v a p hp
  · by_cases hF : FreeLayer P C (Ω.profile T.type) false
    · let f := Value.asPlus hF v
      let key : PlusFrame (hw := hw) Ω C hno := (a.argument, a.plusParameter hF p hp)
      by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) (f.exiting ([],key))
      · exact ⟨.plus (f.slice key), a.free_target hF hA⟩
    · have hM : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      let f := Value.asMinus hM v
      let key : MinusFrame (hw := hw) Ω C hno := (a.argument, a.minusParameter hM p hp)
      by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) ((FreeObservations.behavior _ _ _ _ f).exiting ([],key))
      · exact ⟨.minus (FreeObservations.minusSlice f key), a.free_target hM hA⟩
end PureTypeSystem.ObservationValues


namespace PureTypeSystem
universe u

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)} (e : Environment (hw := hw) Ω C hno Γ)

noncomputable abbrev actualType {M T : Expr S} (h : HasType P Γ M T) : ActualType Ω :=
  ⟨(T.subst e.images).normalForm, (ContextTower.HasType.subst h e.typed).actual_type hw⟩

noncomputable abbrev activeType {M T : Expr S} (h : HasType P Γ M T)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) : ActiveType Ω C :=
  .ofActual (e.actualType h) ha

noncomputable abbrev actualExpression {M : Expr S} {s : S} (h : HasType P Γ M (.sort s)) : ActualType Ω :=
  ⟨(M.subst e.images).normalForm, (ContextTower.HasType.subst h e.typed).actual_expression hw⟩

theorem type_convert_eq {M T N U : Expr S} (hM : HasType P Γ M T)
    (hN : HasType P Γ N U) (hc : Converts T U) :
    (T.subst e.images).normalForm = (U.subst e.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst hM e.typed).type_weaklyNormalizing hw)
    ((ContextTower.HasType.subst hN e.typed).type_weaklyNormalizing hw) (hc.subst _)

theorem expression_convert_eq {M T N U : Expr S} (hM : HasType P Γ M T)
    (hN : HasType P Γ N U) (hc : Converts M N) :
    (M.subst e.images).normalForm = (N.subst e.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst hM e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hN e.typed).weaklyNormalizing hw) (hc.subst _)
end Environment

namespace ProductInstance
variable {Ω C hno}
noncomputable def ofFormation {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno :=
  let h := hp.generation_pi
  { context := Γ
    domain := D
    body := E
    domainSort := h.choose
    bodySort := h.choose_spec.choose
    resultSort := h.choose_spec.choose_spec.choose
    domainTyping := h.choose_spec.choose_spec.choose_spec.1
    bodyTyping := h.choose_spec.choose_spec.choose_spec.2.1
    rule := h.choose_spec.choose_spec.choose_spec.2.2.1
    environment := e }

noncomputable def ofFunction {Γ : List (Expr S)} {f D E : Expr S}
    (hf : HasType P Γ f (.pi D E)) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno :=
  ofFormation hf.product_type_sorted.choose_spec e

variable (t : ProductInstance (hw := hw) Ω C hno)

theorem frame_domain {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : a.domain = t.domainNF := (Expr.pi.inj (a.product.symm.trans he)).1

theorem frame_body {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : a.body = t.bodyNF := (Expr.pi.inj (a.product.symm.trans he)).2

noncomputable def frameEnvironment {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) : Environment (hw := hw) Ω C hno (t.domain :: t.context) :=
  t.extend (t.frame_domain he a ▸ a.typed) p (t.frame_domain he a ▸ hp)

theorem frame_type {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    (t.body.subst (t.frameEnvironment he a p hp).images).normalForm = (a.target hw).type := by
  change t.targetNF a.argument = (a.body.instantiate a.argument).normalForm
  rw [t.target_eq (t.frame_domain he a ▸ a.typed), t.frame_body he a]

/-- A function's normalized argument frame, formed at the exact stored
product, not at an independently chosen derivation of that product. -/
noncomputable def argumentFrame {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (ha : ActiveLayer P C (Ω.profile (t.targetNF n))) : FrameKey Ω C T where
  domain := t.domainNF
  body := t.bodyNF
  product := he
  argument := n.normalForm
  normal := (Expr.normalForm_spec (hn.weaklyNormalizing hw)).2
  typed := hn.normalForm hw
  active := by
    have h1 : (t.bodyNF.instantiate n).normalForm = (t.bodyNF.instantiate n.normalForm).normalForm := by
      have hs := t.target_typed hn
      have hn' := hn.normalForm hw
      have hs' := t.target_typed hn'
      rw [t.target_eq hn] at hs
      rw [t.target_eq hn'] at hs'
      obtain ⟨s, hb⟩ := Ω.frame_target_sorted t.product_typed hn
      obtain ⟨s', hb'⟩ := Ω.frame_target_sorted t.product_typed hn'
      exact Expr.normalForm_converts (hb.weaklyNormalizing hw) (hb'.weaklyNormalizing hw)
        ((Expr.normalForm_spec (hn.weaklyNormalizing hw)).1.converts.instantiate_right t.bodyNF)
    rw [t.target_eq hn, h1] at ha
    simpa only [ContextTower.profile_normalForm] using ha

theorem argumentFrame_type {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (ha : ActiveLayer P C (Ω.profile (t.targetNF n))) :
    ((t.argumentFrame he hn ha).target hw).type = t.targetNF n := by
  change (t.bodyNF.instantiate n.normalForm).normalForm = t.targetNF n
  rw [t.target_eq hn]
  obtain ⟨s, hb⟩ := Ω.frame_target_sorted t.product_typed hn
  obtain ⟨s', hb'⟩ := Ω.frame_target_sorted t.product_typed (hn.normalForm hw)
  exact Expr.normalForm_converts (hb'.weaklyNormalizing hw) (hb.weaklyNormalizing hw)
    (.symm _ _ ((Expr.normalForm_spec (hn.weaklyNormalizing hw)).1.converts.instantiate_right t.bodyNF))
end ProductInstance
end ObservationValues
end PureTypeSystem


/-! Syntax recursion for Val/Read. `PreResult` uses the totalized minus pack;
the source semantics additionally needs the uniform finite-bound theorem,
which must rule out its fallback at every actual lambda. -/
namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace PayloadFits
variable {Ω C hno} {T : Expr S} {p : Option (RawValue (hw := hw) Ω C hno)}
noncomputable def value (hp : PayloadFits Ω C hno T p) (ha : ActiveLayer P C (Ω.profile T)) :
    Value (hw := hw) Ω C hno T := by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => exact ⟨v,hp⟩

theorem value_spec (hp : PayloadFits Ω C hno T p) (ha : ActiveLayer P C (Ω.profile T)) :
    some (hp.value ha).val = p := by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => rfl
end PayloadFits

structure PreResult {Γ : List (Expr S)} (M T : Expr S) (e : Environment (hw := hw) Ω C hno Γ) where
  val : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
    Value (hw := hw) Ω C hno (T.subst e.images).normalForm
  read : Candidate Ω (M.subst e.images).normalForm

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S} {e : Environment (hw := hw) Ω C hno Γ}
noncomputable def parameter (r : PreResult Ω C hno M T e) : Option (RawValue (hw := hw) Ω C hno) :=
  if ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) then some (r.val ha).val else none

theorem parameter_fits (r : PreResult Ω C hno M T e) :
    PayloadFits Ω C hno (T.subst e.images).normalForm r.parameter := by
  unfold parameter
  split
  · exact (r.val _).property
  · assumption

/-- The source base Read clause. For nonliteral expected types this extra
coordinate is unused; no additional semantic assertion is made about it. -/
noncomputable def baseRead (h : HasType P Γ M T)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) :
    Candidate Ω (M.subst e.images).normalForm :=
  if _hm : Ω.profile (M.subst e.images).normalForm ∈ C then
    if hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C then
      if ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) then
        (RawValue.base Ω C hno (v ha).val) (e.actualExpression (hs.choose_spec.1 ▸ h))
      else ⟨_, Candidates.top_candidate⟩
    else ⟨_, Candidates.top_candidate⟩
  else ⟨_, Candidates.top_candidate⟩

noncomputable def baseResult (h : HasType P Γ M T)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) : PreResult Ω C hno M T e :=
  ⟨v, baseRead h v⟩

noncomputable def lookup {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : Converts T A) (e : Environment (hw := hw) Ω C hno Γ) :
    PreResult Ω C hno (.var n) T e := by
  apply baseResult h
  intro ha
  have he : (T.subst e.images).normalForm = (A.subst e.images).normalForm :=
    e.type_convert_eq h (HasType.lookup h.valid hd) hc
  have hp := e.lawful n A hd
  rw [← he] at hp
  exact hp.value ha

noncomputable def sort {s t : S} (h : HasType P Γ (.sort s) T)
    (_ha : P.axioms s t) (_hc : Converts T (.sort t))
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.sort s) T e where
  val ha := distinguished Ω C hno (e.activeType h ha)
  read := ⟨_, Candidates.top_candidate⟩

noncomputable abbrev productData {D E : Expr S} {a b c : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno := ⟨Γ,D,E,a,b,c,hd,hb,hr,e⟩

noncomputable def productCandidate {D E : Expr S} {a b c : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c)
    (ed : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno D (.sort a) e)
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno E (.sort b) e)
    (e : Environment (hw := hw) Ω C hno Γ) : Candidate Ω (Expr.pi D E |>.subst e.images).normalForm := by
  let t := productData hd hb hr e
  let pc := t.candidate (ed e).read (fun n hn p hp => (eb (t.extend hn p hp)).read)
  exact ⟨pc.val,t.product_nf.symm ▸ pc.property⟩

noncomputable def product {D E : Expr S} {a b c : S} (h : HasType P Γ (.pi D E) T)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (_hc : Converts T (.sort c))
    (ed : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno D (.sort a) e)
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno E (.sort b) e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.pi D E) T e := by
  let pc := productCandidate hd hb hr ed eb e
  refine ⟨?_, ?_⟩
  · intro ha
    if hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C then
      exact withBase Ω C hno (e.activeType h ha)
        (Base.update Ω (topBase Ω) (e.actualExpression (.product hd hb hr)) pc)
    else exact distinguished Ω C hno (e.activeType h ha)
  · exact if Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C then pc
      else ⟨_, Candidates.top_candidate⟩

noncomputable def abstractionAction {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno m E e)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    LambdaAction (hw := hw) Ω C hno (e.activeType h ha) := by
  let t := ProductInstance.ofFormation hp e
  let A := e.activeType h ha
  have he : A.type = .pi t.domainNF t.bodyNF := by
    exact (Expr.normalForm_converts ((ContextTower.HasType.subst h e.typed).type_weaklyNormalizing hw)
      ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw) (hc.subst e.images)).trans t.product_nf
  intro k p hk
  let e' := t.frameEnvironment he k p hk
  have he' : (E.subst e'.images).normalForm = (k.target hw).type := t.frame_type he k p hk
  have ha' : ActiveLayer P C (Ω.profile (E.subst e'.images).normalForm) := he' ▸ (k.target hw).active
  exact ⟨((eb e').val ha').val, he' ▸ ((eb e').val ha').property⟩

noncomputable def abstraction {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno m E e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.lam D m) T e :=
  baseResult h fun ha => lambdaValue Ω C hno (e.activeType h ha) (abstractionAction h hp hc eb e ha)

noncomputable def applicationValue {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno f (.pi D E) e)
    (en : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno n D e)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    Value (hw := hw) Ω C hno (T.subst e.images).normalForm := by
  let Ta := e.activeType h ha
  by_cases hF : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm)
  · let t := ProductInstance.ofFunction hf e
    let Fa := e.activeType hf hF
    have he : Fa.type = .pi t.domainNF t.bodyNF := t.product_nf
    have hn' : Ω.HasType (n.subst e.images) t.domainNF :=
      (ContextTower.HasType.subst hn e.typed).normalize_type hw
    have ht : (T.subst e.images).normalForm = t.targetNF (n.subst e.images) := by
      have hh := e.type_convert_eq h (HasType.application hf hn) hc
      simpa only [ProductInstance.targetNF, ProductInstance.rawTarget,
        t, ProductInstance.ofFunction, ProductInstance.ofFormation,
        ← Expr.instantiate_subst, Expr.instantiate_liftSub] using hh
    have ha' : ActiveLayer P C (Ω.profile (t.targetNF (n.subst e.images))) := ht ▸ ha
    let k := t.argumentFrame he hn' ha'
    have hk : (k.target hw).type = (T.subst e.images).normalForm :=
      (t.argumentFrame_type he hn' ha').trans ht.symm
    let v := applyValue Ω C hno Fa ((ef e).val hF) k (en e).parameter (en e).parameter_fits
    exact ⟨v.val, hk ▸ v.property⟩
  · exact distinguished Ω C hno Ta
noncomputable def application {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno f (.pi D E) e)
    (en : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno n D e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.app f n) T e :=
  baseResult h fun ha => applicationValue h hf hn hc ef en e ha
end PreResult

/-- Structural recursion retaining every stored role choice.
The annotation child at a lambda is immaterial to its observation value,
but is retained in the input tree for the fundamental normalization lemma.
Representability follows from the uniform finite-bound theorem. -/
noncomputable def preEvaluate {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) :
    ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno M T e := by
  induction t with
  | var h hd hc => exact PreResult.lookup h hd hc
  | sort h ha hc => exact PreResult.sort h ha hc
  | product h d b hr hc ihd ihb => exact PreResult.product h d.typing b.typing hr hc ihd ihb
  | abstraction h d b hp hc ihd ihb => exact PreResult.abstraction h hp hc ihb
  | application h f a hc ihf iha => exact PreResult.application h f.typing a.typing hc ihf iha

end PureTypeSystem.ObservationValues

end OAI
