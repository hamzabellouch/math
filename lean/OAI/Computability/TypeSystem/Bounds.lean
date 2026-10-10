import OAI.Computability.TypeSystem.Evaluation

namespace OAI

namespace PureTypeSystem.ObservationValues

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace RawValue
variable {Ω C hno}
theorem level_symm {n : Nat} {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq Ω C hno n v w) : LevelEq Ω C hno n w v := by
  cases v <;> cases w <;> try exact False.elim he
  · exact Eq.symm he
  · exact FreeObservations.Agree.symm he
  · exact Eq.symm he

theorem level_trans {n : Nat} {v w z : RawValue (hw := hw) Ω C hno}
    (he : LevelEq Ω C hno n v w) (hf : LevelEq Ω C hno n w z) : LevelEq Ω C hno n v z := by
  cases v <;> cases w <;> cases z <;> dsimp only [LevelEq] at he hf ⊢
  all_goals first | exact False.elim he | exact False.elim hf | exact Eq.trans he hf

theorem level_fits {n : Nat} {T : Expr S} {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq Ω C hno n v w) : Fits Ω C hno T v ↔ Fits Ω C hno T w := by
  cases v <;> cases w <;> try exact False.elim he
  · exact he ▸ Iff.rfl
  · rfl
  · rfl

theorem level_eq_of_plain {n : Nat} {T : Expr S} (hT : PlainLayer P C (Ω.profile T))
    {v w : RawValue (hw := hw) Ω C hno} (hv : Fits Ω C hno T v)
    (he : LevelEq Ω C hno n v w) : v = w := by
  cases v with
  | plus p => exact False.elim (hv.1 hT)
  | minus p => exact False.elim (hv.1 hT)
  | plain p =>
    cases w with
    | plain q => exact congrArg RawValue.plain he
    | plus _ | minus _ => exact False.elim he

theorem bounded_of_not_minus {n : Nat} {T : Expr S}
    (hT : ¬ FreeLayer P C (Ω.profile T) true)
    {v : RawValue (hw := hw) Ω C hno} (hv : Fits Ω C hno T v) : Bounded Ω C hno n v := by
  cases v with
  | plain _ | plus _ => trivial
  | minus _ => exact False.elim (hT hv)
end RawValue

namespace Parameter
variable {Ω C hno}
theorem level_symm {n : Nat} {p q : Option (RawValue (hw := hw) Ω C hno)}
    (he : LevelEq Ω C hno n p q) : LevelEq Ω C hno n q p := by
  cases p <;> cases q <;> try exact he
  exact RawValue.level_symm he

theorem level_fits {n : Nat} {T : Expr S} {p q : Option (RawValue (hw := hw) Ω C hno)}
    (he : LevelEq Ω C hno n p q) : PayloadFits Ω C hno T p ↔ PayloadFits Ω C hno T q := by
  cases p <;> cases q <;> try exact False.elim he
  · rfl
  · exact RawValue.level_fits he

theorem bounded_of_not_minus {n : Nat} {T : Expr S}
    (hT : ¬ FreeLayer P C (Ω.profile T) true)
    {p : Option (RawValue (hw := hw) Ω C hno)} (hp : PayloadFits Ω C hno T p) : Bounded Ω C hno n p := by
  intro v hv
  subst p
  exact RawValue.bounded_of_not_minus hT hp

theorem bounded_none (n : Nat) : Bounded (hw := hw) Ω C hno n none := fun _ h => by cases h
end Parameter

namespace Value
variable {Ω C hno}
theorem level_asPlus {n : Nat} {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    {v w : Value (hw := hw) Ω C hno T}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) :
    FreeObservations.Agree n (asPlus hT v) (asPlus hT w) := by
  rw [asPlus_spec hT v, asPlus_spec hT w] at he
  exact he

theorem level_asMinus {n : Nat} {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    {v w : Value (hw := hw) Ω C hno T}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) : asMinus hT v = asMinus hT w := by
  rw [asMinus_spec hT v, asMinus_spec hT w] at he
  exact he

theorem bounded_asMinus {n : Nat} {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    {v : Value (hw := hw) Ω C hno T} (hv : RawValue.Bounded Ω C hno n v.val) :
    FreeObservations.InStage n (asMinus hT v) := by
  rw [asMinus_spec hT v] at hv
  exact hv
end Value

theorem distinguished_bounded (T : ActiveType Ω C) :
    RawValue.Bounded Ω C hno 1 (distinguished (hw := hw) Ω C hno T).val := by
  unfold distinguished
  split
  · trivial
  · split
    · trivial
    · exact ⟨_,rfl⟩

theorem withBase_bounded (T : ActiveType Ω C) (b : Base Ω) :
    RawValue.Bounded Ω C hno 1 (withBase (hw := hw) Ω C hno T b).val := by
  unfold withBase
  split
  · trivial
  · split
    · trivial
    · exact ⟨_,rfl⟩

theorem tagPlain_level {n : Nat} (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    {v w : Value (hw := hw) Ω C hno T.type}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) :
    tagPlain Ω C hno T hp v = tagPlain Ω C hno T hp w := by
  apply RawValue.plain.inj
  rw [tagPlain_spec,tagPlain_spec]
  exact RawValue.level_eq_of_plain hp v.property he

namespace Gate
variable {Ω C hno}
theorem level_iff {n : Nat} {T : ActiveType Ω C} {q : Expr S} {e : Bool}
    {p p' : Option (RawValue (hw := hw) Ω C hno)} (he : Parameter.LevelEq Ω C hno n p p') :
    Gate Ω C hno T q p e ↔ Gate Ω C hno T q p' e := by
  constructor
  · rintro ⟨a,ha,hp,hf⟩
    exact ⟨a,ha,(Parameter.level_fits he).mp hp,hf⟩
  · rintro ⟨a,ha,hp,hf⟩
    exact ⟨a,ha,(Parameter.level_fits he).mpr hp,hf⟩
end Gate

theorem plusPayload_bounded {n : Nat} (a : PlusFrame (hw := hw) Ω C hno)
    (ha : FreeObservations.FrameBound n a) : Parameter.Bounded Ω C hno n (plusPayload Ω C hno a.2) := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact Parameter.bounded_none n
  | plain p => intro v hv; cases hv; trivial
  | opposite p => intro v hv; cases hv; exact ha p rfl

theorem minusPayload_bounded (n : Nat) (a : MinusFrame (hw := hw) Ω C hno) :
    Parameter.Bounded Ω C hno n (minusPayload Ω C hno a.2) := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact Parameter.bounded_none n
  | plain p | opposite p => intro v hv; cases hv; trivial

theorem minusFrame_restrict {n : Nat} {a a' : MinusFrame (hw := hw) Ω C hno}
    (ha : FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a') :
    a.1 = a'.1 ∧ Parameter.LevelEq Ω C hno n (minusPayload Ω C hno a.2) (minusPayload Ω C hno a'.2) := by
  rcases a with ⟨q,p⟩
  rcases a' with ⟨q',p'⟩
  have hh := Prod.mk.inj ha
  refine ⟨hh.1,?_⟩
  cases p <;> cases p' <;> dsimp only [FreeObservations.Payload.map, minusPayload,
    Parameter.LevelEq, RawValue.LevelEq] at hh ⊢
  all_goals first | exact True.intro | exact FreeObservations.Payload.plain.inj hh.2 |
    exact FreeObservations.Payload.opposite.inj hh.2 | cases hh.2

/-- The local induction hypotheses used at a lambda. -/
def ActionBound (T : ActiveType Ω C) (k l : Nat) (act : LambdaAction (hw := hw) Ω C hno T) : Prop :=
  ∀ a p hp, Parameter.Bounded Ω C hno k p → RawValue.Bounded Ω C hno l (act a p hp).val

def ActionRelated (T : ActiveType Ω C) (k l : Nat)
    (act act' : LambdaAction (hw := hw) Ω C hno T) : Prop :=
  ∀ a p p' hp hp', Parameter.Bounded Ω C hno k p → Parameter.Bounded Ω C hno k p' →
    Parameter.LevelEq Ω C hno l p p' → RawValue.LevelEq Ω C hno k (act a p hp).val (act' a p' hp').val

namespace LambdaAction
variable {Ω C hno}
theorem frame_congr {T : ActiveType Ω C} (act : LambdaAction (hw := hw) Ω C hno T)
    {a b : FrameKey Ω C T} (he : a = b) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hq : PayloadFits Ω C hno b.domain p) :
    (act a p hp).val = (act b p hq).val := by
  cases he
  rfl
end LambdaAction

namespace ActionRelated
variable {Ω C hno}
theorem gates {T : ActiveType Ω C} {k l : Nat} {act act' : LambdaAction (hw := hw) Ω C hno T}
    (hr : ActionRelated Ω C hno T k l act act')
    {q q' : Expr S} (hq : q = q') {ex : Bool}
    {p p' : Option (RawValue (hw := hw) Ω C hno)}
    (h : Gate Ω C hno T q p ex) (h' : Gate Ω C hno T q' p' ex)
    (hb : Parameter.Bounded Ω C hno k p) (hb' : Parameter.Bounded Ω C hno k p')
    (he : Parameter.LevelEq Ω C hno l p p') :
    RawValue.LevelEq Ω C hno k (act h.frame p h.payload).val (act' h'.frame p' h'.payload).val := by
  have hf : h.frame = h'.frame := FrameKey.ext (h.argument.trans (hq.trans h'.argument.symm))
  have hp' : PayloadFits Ω C hno h.frame.domain p' := hf.symm ▸ h'.payload
  have hh := hr h.frame p p' h.payload hp' hb hb' he
  rw [LambdaAction.frame_congr act' hf p' hp' h'.payload] at hh
  exact hh
end ActionRelated

theorem minusContinue_bounded {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat} (hl : 1 ≤ l)
    {act : LambdaAction (hw := hw) Ω C hno T} (hb : ActionBound Ω C hno T k l act)
    (a : MinusFrame (hw := hw) Ω C hno) :
    FreeObservations.InStage l (minusContinue Ω C hno T hT act a) := by
  unfold minusContinue
  split
  · exact Value.bounded_asMinus _ (hb _ _ _ (minusPayload_bounded Ω C hno k a))
  · exact FreeObservations.InStage.mono hl ⟨_,rfl⟩

theorem minusContinue_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act')
    {a a' : MinusFrame (hw := hw) Ω C hno}
    (ha : FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ l) a =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ l) a') :
    minusContinue Ω C hno T hT act a = minusContinue Ω C hno T hT act' a' := by
  have hh := minusFrame_restrict Ω C hno ha
  have hg : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false ↔
      Gate Ω C hno T a'.1 (minusPayload Ω C hno a'.2) false := by
    rw [hh.1]
    exact Gate.level_iff hh.2
  unfold minusContinue
  by_cases h : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false
  · have h' := hg.mp h
    rw [dite_eq_left h,dite_eq_left h']
    have he := hr.gates hh.1 h h' (minusPayload_bounded Ω C hno k a)
      (minusPayload_bounded Ω C hno k a') hh.2
    rw [Value.asMinus_spec (h.frame.free_target hT h.not_plain) (act _ _ _),
      Value.asMinus_spec (h'.frame.free_target hT h'.not_plain) (act' _ _ _)] at he
    exact he
  · rw [dite_eq_right h,dite_eq_right (mt hg.mpr h)]

theorem lambdaExit_level {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    {T : ActiveType Ω C} {k l : Nat} {act act' : LambdaAction (hw := hw) Ω C hno T}
    (hr : ActionRelated Ω C hno T k l act act')
    {a a' : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X}
    (hq : a.1 = a'.1) (hb : Parameter.Bounded Ω C hno k (decode a.2))
    (hb' : Parameter.Bounded Ω C hno k (decode a'.2))
    (he : Parameter.LevelEq Ω C hno l (decode a.2) (decode a'.2)) :
    lambdaExit Ω C hno decode T act a = lambdaExit Ω C hno decode T act' a' := by
  have hg : Gate Ω C hno T a.1 (decode a.2) true ↔ Gate Ω C hno T a'.1 (decode a'.2) true := by
    rw [hq]
    exact Gate.level_iff he
  unfold lambdaExit
  by_cases h : Gate Ω C hno T a.1 (decode a.2) true
  · have h' := hg.mp h
    rw [dite_eq_left h,dite_eq_left h']
    have hh := hr.gates hq h h' hb hb' he
    rw [← tagPlain_spec Ω C hno (h.frame.target hw) h.plain (act _ _ _),
      ← tagPlain_spec Ω C hno (h'.frame.target hw) h'.plain (act' _ _ _)] at hh
    exact congrArg some hh
  · rw [dite_eq_right h,dite_eq_right (mt hg.mpr h)]

/-- Uniform body estimates prove the *exact* minus lambda table is in the
colimit, so no fallback in `packMinus` is used. -/
theorem minusLambda_representable {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat} (hl : 1 ≤ l)
    {act : LambdaAction (hw := hw) Ω C hno T} (hb : ActionBound Ω C hno T k l act)
    (hr : ActionRelated Ω C hno T k l act act) :
    ∃ x, FreeObservations.InStage (l+1) x ∧
      FreeObservations.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act := by
  apply FreeObservations.lambdaTable_representable (topBase Ω) none l
  · intro a
    exact (minusContinue_bounded Ω C hno hT hl hb a).mono (Nat.le_succ l)
  · intro a a' ha
    exact minusContinue_level Ω C hno hT hr ha
  · intro a a' ha
    have hh := minusFrame_restrict Ω C hno ha
    exact lambdaExit_level Ω C hno (minusPayload Ω C hno) hr hh.1
      (minusPayload_bounded Ω C hno k a) (minusPayload_bounded Ω C hno k a') hh.2

namespace Value
variable {Ω C hno}
theorem level_asPlain {n : Nat} (T : ActualPlain.Node Ω C)
    {v w : Value (hw := hw) Ω C hno T.type}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) : asPlain T v = asPlain T w := by
  have hh : v = w := Subtype.ext (RawValue.level_eq_of_plain T.plain v.property he)
  exact congrArg (asPlain T) hh
end Value

namespace ActualPlainKey
variable {Ω C hno}
theorem payload_bounded {T : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C T)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a)
    (k : Nat) : Parameter.Bounded Ω C hno k (payload a p) := by
  unfold payload
  split
  · intro v hv
    cases hv
    trivial
  · exact Parameter.bounded_none k
end ActualPlainKey

theorem plainLambda_level {T : ActiveType Ω C} (hT : PlainLayer P C (Ω.profile T.type))
    {k l : Nat} {act act' : LambdaAction (hw := hw) Ω C hno T}
    (hr : ActionRelated Ω C hno T k l act act') :
    RawValue.LevelEq Ω C hno k (plainLambda Ω C hno T hT act).val
      (plainLambda Ω C hno T hT act').val := by
  unfold plainLambda
  change Sigma.mk _ _ = Sigma.mk _ _
  congr 1
  apply congrArg (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)).symm
  apply Prod.ext
  · rfl
  funext a p
  apply Value.level_asPlain
  exact hr _ _ _ _ _ (ActualPlainKey.payload_bounded a p k)
    (ActualPlainKey.payload_bounded a p k) (Parameter.level_refl l _)

theorem plusContinue_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) false) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act')
    (a : PlusFrame (hw := hw) Ω C hno) (ha : FreeObservations.FrameBound k a) :
    FreeObservations.Agree k (plusContinue Ω C hno T hT act a) (plusContinue Ω C hno T hT act' a) := by
  unfold plusContinue
  split
  · exact Value.level_asPlus _ (hr _ _ _ _ _ (plusPayload_bounded Ω C hno a ha)
      (plusPayload_bounded Ω C hno a ha) (Parameter.level_refl l _))
  · exact .refl _ _

theorem plusLambda_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) false) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act') :
    FreeObservations.Agree k (plusLambda Ω C hno T hT act) (plusLambda Ω C hno T hT act') := by
  apply FreeObservations.Agree.of_observations
  · intro as has
    cases as with
    | nil => rfl
    | cons a as =>
      exact (plusContinue_level Ω C hno hT hr a (has a List.mem_cons_self)).continuing
        (fun x hx => has x (List.mem_cons_of_mem _ hx))
  · rintro ⟨as,e⟩ ⟨has,hes⟩
    cases as with
    | nil =>
      exact lambdaExit_level Ω C hno (plusPayload Ω C hno) hr rfl
        (plusPayload_bounded Ω C hno e hes) (plusPayload_bounded Ω C hno e hes) (Parameter.level_refl l _)
    | cons a as =>
      exact (plusContinue_level Ω C hno hT hr a (has a List.mem_cons_self)).exiting
        ⟨fun x hx => has x (List.mem_cons_of_mem _ hx),hes⟩

theorem minusLambdaBehavior_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act') :
    minusLambdaBehavior Ω C hno T hT act = minusLambdaBehavior Ω C hno T hT act' := by
  unfold minusLambdaBehavior
  congr 1
  · funext a
    exact minusContinue_level Ω C hno hT hr rfl
  · funext a
    exact lambdaExit_level Ω C hno (minusPayload Ω C hno) hr rfl
      (minusPayload_bounded Ω C hno k a) (minusPayload_bounded Ω C hno k a) (Parameter.level_refl l _)

theorem lambdaValue_bounded {T : ActiveType Ω C} {k l : Nat} (hl : 1 ≤ l)
    {act : LambdaAction (hw := hw) Ω C hno T} (hb : ActionBound Ω C hno T k l act)
    (hr : ActionRelated Ω C hno T k l act act) :
    RawValue.Bounded Ω C hno (l+1) (lambdaValue Ω C hno T act).val := by
  unfold lambdaValue
  split
  · trivial
  · split
    · trivial
    · exact packMinus_stage Ω C hno _ (minusLambda_representable Ω C hno _ hl hb hr)

theorem lambdaValue_level {T : ActiveType Ω C} {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act') :
    RawValue.LevelEq Ω C hno k (lambdaValue Ω C hno T act).val (lambdaValue Ω C hno T act').val := by
  unfold lambdaValue
  split
  · exact plainLambda_level Ω C hno _ hr
  · split
    · exact plusLambda_level Ω C hno _ hr
    · exact congrArg (packMinus Ω C hno) (minusLambdaBehavior_level Ω C hno _ hr)

namespace RawValue
variable {Ω C hno}
theorem level_eq_of_not_plus {n : Nat} {T : Expr S} (hT : ¬ FreeLayer P C (Ω.profile T) false)
    {v w : RawValue (hw := hw) Ω C hno} (hv : Fits Ω C hno T v)
    (he : LevelEq Ω C hno n v w) : v = w := by
  cases v <;> cases w <;> dsimp only [LevelEq] at he
  all_goals first | exact False.elim he | exact False.elim (hT hv) |
    exact congrArg RawValue.plain he | exact congrArg RawValue.minus he
end RawValue

namespace Parameter
variable {Ω C hno}
theorem level_eq_of_not_plus {n : Nat} {T : Expr S} (hT : ¬ FreeLayer P C (Ω.profile T) false)
    {p q : Option (RawValue (hw := hw) Ω C hno)} (hp : PayloadFits Ω C hno T p)
    (he : LevelEq Ω C hno n p q) : p = q := by
  cases p <;> cases q
  · rfl
  · exact False.elim he
  · exact False.elim he
  · exact congrArg some (RawValue.level_eq_of_not_plus hT hp he)
end Parameter

theorem minusFrame_restrict_of_level {n : Nat} {a a' : MinusFrame (hw := hw) Ω C hno}
    (hq : a.1 = a'.1)
    (he : Parameter.LevelEq Ω C hno n (minusPayload Ω C hno a.2) (minusPayload Ω C hno a'.2)) :
    FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a' := by
  rcases a with ⟨q,p⟩
  rcases a' with ⟨q',p'⟩
  cases p <;> cases p' <;> dsimp only [minusPayload,Parameter.LevelEq,RawValue.LevelEq] at he
  all_goals first | exact False.elim he |
    exact Prod.ext hq rfl |
    exact Prod.ext hq (congrArg FreeObservations.Payload.plain he) |
    exact Prod.ext hq (congrArg FreeObservations.Payload.opposite he)

namespace FrameKey
variable {Ω C hno} {T : ActiveType Ω C} (a : FrameKey Ω C T)
theorem plusParameter_bound (hT : FreeLayer P C (Ω.profile T.type) false)
    {n : Nat} (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hb : Parameter.Bounded Ω C hno n p) :
    FreeObservations.FrameBound n (a.argument,a.plusParameter hT p hp) := by
  cases p with
  | none => intro x hx; cases hx
  | some v =>
    cases v with
    | plain p => intro x hx; cases hx
    | plus p => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
    | minus p =>
      intro x hx
      have hh : p = x := FreeObservations.Payload.opposite.inj hx
      exact hh ▸ hb _ rfl

theorem minusParameter_level (hT : FreeLayer P C (Ω.profile T.type) true)
    {n : Nat} (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a.domain p')
    (he : Parameter.LevelEq Ω C hno n p p') :
    FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) (a.argument,a.minusParameter hT p hp) =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) (a.argument,a.minusParameter hT p' hp') := by
  apply minusFrame_restrict_of_level Ω C hno
  · rfl
  · simpa only [minusPayload_parameter] using he
end FrameKey

theorem applyValue_bounded {T : ActiveType Ω C} {n : Nat} (v : Value (hw := hw) Ω C hno T.type)
    (hv : RawValue.Bounded Ω C hno n v.val) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    RawValue.Bounded Ω C hno n (applyValue Ω C hno T v a p hp).val := by
  unfold applyValue
  split
  · trivial
  · split
    · split
      · rename_i ht
        exact RawValue.bounded_of_not_minus (fun h => h.1 ht) (exitValue Ω C hno _ _).property
      · trivial
    · split
      · rename_i ht
        exact RawValue.bounded_of_not_minus (fun h => h.1 ht) (exitValue Ω C hno _ _).property
      · exact FreeObservations.inStage_minusSlice (topBase Ω) none (Value.bounded_asMinus _ hv) _

theorem applyValue_level {T : ActiveType Ω C} {k j r : Nat}
    (v v' : Value (hw := hw) Ω C hno T.type) (hv : RawValue.Bounded Ω C hno j v.val)
    (hvv : RawValue.LevelEq Ω C hno (max k r) v.val v'.val) (a : FrameKey Ω C T)
    (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a.domain p')
    (hb : Parameter.Bounded Ω C hno r p) (hpp : Parameter.LevelEq Ω C hno j p p') :
    RawValue.LevelEq Ω C hno k (applyValue Ω C hno T v a p hp).val
      (applyValue Ω C hno T v' a p' hp').val := by
  unfold applyValue
  by_cases hT : PlainLayer P C (Ω.profile T.type)
  · rw [dite_eq_left hT,dite_eq_left hT]
    have hvv' : v = v' := Subtype.ext (RawValue.level_eq_of_plain hT v.property hvv)
    have hpp' : p = p' := Parameter.level_eq_of_not_plus
      (fun hf => hf.1 (a.plain_domain hw hT hf.active)) hp hpp
    subst v'
    subst p'
    exact RawValue.level_refl k _
  · rw [dite_eq_right hT,dite_eq_right hT]
    by_cases hF : FreeLayer P C (Ω.profile T.type) false
    · rw [dite_eq_left hF,dite_eq_left hF]
      have hpp' : p = p' := Parameter.level_eq_of_not_plus
        (fun hf => Bool.noConfusion (a.free_domain_sign hw hF hf)) hp hpp
      subst p'
      have hh := Value.level_asPlus hF hvv
      have ha := (a.plusParameter_bound hF p hp hb).mono (le_max_right k r)
      split
      · have he := hh.exiting (as := ([],(a.argument,a.plusParameter hF p hp)))
          ⟨fun x hx => False.elim (List.not_mem_nil hx),ha⟩
        dsimp only
        rw [he]
        exact RawValue.level_refl k _
      · exact hh.slice (le_max_left k r) _ ha
    · rw [dite_eq_right hF,dite_eq_right hF]
      have hM : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with hh | hh | hh
        · exact False.elim (hT hh)
        · exact False.elim (hF hh)
        · exact hh
      have hh := Value.level_asMinus hM hvv
      have hs := (Value.bounded_asMinus hM hv).mono (Nat.le_succ j)
      have ha := a.minusParameter_level hM p p' hp hp' hpp
      split
      · dsimp only
        rw [← hh]
        have he := FreeObservations.minusExit_eq_of_restrict (topBase Ω) none hs ha
        rw [he]
        exact RawValue.level_refl k _
      · change FreeObservations.minusSlice _ _ = FreeObservations.minusSlice _ _
        rw [← hh]
        exact FreeObservations.minusSlice_eq_of_restrict (topBase Ω) none hs ha

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}
theorem imageCompatible_symm {e f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f) :
    f.ImageCompatible e := fun n hn => (he n hn).symm

theorem level_symm {e f : Environment (hw := hw) Ω C hno Γ} {k : Nat} (he : e.LevelEq k f) :
    f.LevelEq k e := ⟨imageCompatible_symm he.1, fun n hn => Parameter.level_symm (he.2 n hn)⟩

theorem level_cons {e f : Environment (hw := hw) Ω C hno Γ} {k : Nat}
    (he : e.LevelEq k f) {A a b : Expr S} (ha : Ω.HasType a (A.subst e.images))
    (hb : Ω.HasType b (A.subst f.images)) (hab : Converts a b)
    (p q : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    (hq : PayloadFits Ω C hno (A.subst f.images).normalForm q)
    (hpq : Parameter.LevelEq Ω C hno k p q) :
    (e.cons ha p hp).LevelEq k (f.cons hb q hq) := by
  constructor
  · intro n hn
    cases n with
    | zero => exact hab
    | succ n => exact he.1 n (Nat.lt_of_succ_lt_succ hn)
  · intro n hn
    cases n with
    | zero => exact hpq
    | succ n => exact he.2 n (Nat.lt_of_succ_lt_succ hn)
end Environment

namespace Value
variable {Ω C hno}
@[simp] theorem cast_val {T U : Expr S} (h : T = U) (v : Value (hw := hw) Ω C hno T) :
    (h ▸ v).val = v.val := by subst U; rfl
end Value

theorem lambdaValue_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type)
    {k l : Nat} (act : LambdaAction (hw := hw) Ω C hno T)
    (act' : LambdaAction (hw := hw) Ω C hno U)
    (hr : ∀ (a : FrameKey Ω C T) (a' : FrameKey Ω C U), a.argument = a'.argument →
      ∀ p p' hp hp', Parameter.Bounded Ω C hno k p → Parameter.Bounded Ω C hno k p' →
      Parameter.LevelEq Ω C hno l p p' →
      RawValue.LevelEq Ω C hno k (act a p hp).val (act' a' p' hp').val) :
    RawValue.LevelEq Ω C hno k (lambdaValue Ω C hno T act).val (lambdaValue Ω C hno U act').val := by
  have hu := ActiveType.ext hTU
  subst U
  exact lambdaValue_level Ω C hno (fun a p p' hp hp' hb hb' he => hr a a rfl p p' hp hp' hb hb' he)

theorem applyValue_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type)
    {k j r : Nat} (v : Value (hw := hw) Ω C hno T.type) (v' : Value (hw := hw) Ω C hno U.type)
    (hv : RawValue.Bounded Ω C hno j v.val)
    (hvv : RawValue.LevelEq Ω C hno (max k r) v.val v'.val)
    (a : FrameKey Ω C T) (a' : FrameKey Ω C U) (hq : a.argument = a'.argument)
    (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a'.domain p')
    (hb : Parameter.Bounded Ω C hno r p) (hpp : Parameter.LevelEq Ω C hno j p p') :
    RawValue.LevelEq Ω C hno k (applyValue Ω C hno T v a p hp).val
      (applyValue Ω C hno U v' a' p' hp').val := by
  have hu := ActiveType.ext hTU
  subst U
  have ha := FrameKey.ext hq
  subst a'
  exact applyValue_level Ω C hno v v' hv hvv a p p' hp hp' hb hpp

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
variable {e f : Environment (hw := hw) Ω C hno Γ}

theorem parameter_eq (r : PreResult Ω C hno M T e)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    r.parameter = some (r.val ha).val := dite_eq_left ha

theorem parameter_bounded {k : Nat} (r : PreResult Ω C hno M T e)
    (hb : ∀ ha, RawValue.Bounded Ω C hno k (r.val ha).val) :
    Parameter.Bounded Ω C hno k r.parameter := by
  unfold parameter
  split
  · intro v hv
    exact Option.some.inj hv ▸ hb _
  · exact Parameter.bounded_none k

theorem val_bounded {k : Nat} (r : PreResult Ω C hno M T e)
    (hb : Parameter.Bounded Ω C hno k r.parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    RawValue.Bounded Ω C hno k (r.val ha).val := hb _ (r.parameter_eq ha)

theorem parameter_level {k : Nat} (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M T f)
    (ht : (T.subst e.images).normalForm = (T.subst f.images).normalForm)
    (hv : ∀ ha hb, RawValue.LevelEq Ω C hno k (r.val ha).val (q.val hb).val) :
    Parameter.LevelEq Ω C hno k r.parameter q.parameter := by
  unfold parameter
  by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
  · have hb := ht ▸ ha
    rw [dite_eq_left ha,dite_eq_left hb]
    exact hv ha hb
  · have hb : ¬ ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) := ht ▸ ha
    rw [dite_eq_right ha,dite_eq_right hb]
    trivial

theorem val_level {k : Nat} (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M T f)
    (hr : Parameter.LevelEq Ω C hno k r.parameter q.parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k (r.val ha).val (q.val hb).val := by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact hr

 theorem baseRead_level {k : Nat} (h : HasType P Γ M T) (he : e.ImageCompatible f)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm)
    (w : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst f.images).normalForm)
    (hv : ∀ ha hb, RawValue.LevelEq Ω C hno k (v ha).val (w hb).val) :
    (baseRead h v).val = (baseRead h w).val := by
  have hM := e.actual_expr_eq he h
  have hT := e.actual_type_eq he h
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile (M.subst f.images).normalForm ∈ C := hM ▸ hm
    by_cases hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C
    · by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
      · have hb : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead, Environment.actualExpression, hm, hm', hs, ha, hb, dite_true]
        have hbase := RawValue.level_base (hv ha hb)
        have hX : e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs.choose_spec.1 ▸ h) := Subtype.ext hM
        dsimp only [Environment.actualExpression] at hX
        rw [hbase]
        exact congrArg (fun X : ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb : ¬ ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead, Environment.actualExpression, hm, hm', hs, ha, hb, dite_true, dite_false]
        exact congrArg (Candidates.Top Ω) hM
    · simp only [baseRead, Environment.actualExpression, hm, hm', hs, dite_true, dite_false]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.profile (M.subst f.images).normalForm ∉ C := hM ▸ hm
    simp only [baseRead, Environment.actualExpression, hm, hm', dite_false]
    exact congrArg (Candidates.Top Ω) hM

end PreResult

namespace ProductInstance
variable {Ω C hno}
theorem domain_not_minus (t : ProductInstance (hw := hw) Ω C hno)
    (hC : IsComponent (PrimaryEdge P) C) {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (hK : Ω.profile (.pi t.domainNF t.bodyNF) ∈ C) (hL : Ω.profile (t.targetNF n) ∈ C) :
    ¬ FreeLayer P C (Ω.profile t.domainNF) true := by
  intro hm
  obtain ⟨J,hf,hp⟩ := Ω.frame_profiles hw t.product_typed hn
  have hL' : Ω.profile (t.bodyNF.instantiate n) ∈ C := by
    rw [t.target_eq hn,ContextTower.profile_normalForm] at hL
    exact hL
  have hJ := hC.between hL' hK hp.reach (.single (.codomain hf))
  exact Bool.noConfusion (hm.direct_sign ⟨hm.active.layer,J,hJ,_,hK,hf⟩)

theorem targetNF_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (hE : t.bodyNF = t'.bodyNF)
    {n : Expr S} (hn : Ω.HasType n t.domainNF) : t.targetNF n = t'.targetNF n := by
  rw [t.target_eq hn,t'.target_eq (hD ▸ hn),hE]

theorem testers_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (d : Candidate Ω t.domainNF) (d' : Candidate Ω t'.domainNF)
    (hd : Ω.profile t.domainNF ∈ C → d.val = d'.val) : t.testers d = t'.testers d' := by
  unfold testers
  by_cases hh : Ω.profile t.domainNF ∈ C
  · have hh' : Ω.profile t'.domainNF ∈ C := hD ▸ hh
    rw [ite_eq_left hh,ite_eq_left hh']
    exact hd hh
  · have hh' : Ω.profile t'.domainNF ∉ C := hD ▸ hh
    rw [ite_eq_right hh,ite_eq_right hh',hD]

theorem fibers_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (hE : t.bodyNF = t'.bodyNF)
    (b : t.BodyReads) (b' : t'.BodyReads)
    (hb : ∀ n hn p hp, Ω.profile (t.targetNF n) ∈ C →
        (b n hn p hp).val = (b' n (hD ▸ hn) p (hD ▸ hp)).val) :
    t.fibers b = t'.fibers b' := by
  funext n
  unfold fibers
  by_cases hn : Ω.HasType n t.domainNF
  · have hn' : Ω.HasType n t'.domainNF := hD ▸ hn
    rw [dite_eq_left hn,dite_eq_left hn']
    have ht := targetNF_eq hD hE hn
    by_cases hc : Ω.profile (t.targetNF n) ∈ C
    · have hc' : Ω.profile (t'.targetNF n) ∈ C := ht ▸ hc
      rw [ite_eq_left hc,ite_eq_left hc']
      ext U
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hD ▸ hp,hb n hn p hp hc⟩
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hD.symm ▸ hp,(hb n hn p (hD.symm ▸ hp) hc).symm⟩
    · have hc' : Ω.profile (t'.targetNF n) ∉ C := ht ▸ hc
      rw [ite_eq_right hc,ite_eq_right hc',ht]
  · have hn' : ¬ Ω.HasType n t'.domainNF := hD ▸ hn
    rw [dite_eq_right hn,dite_eq_right hn']

theorem candidate_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (hE : t.bodyNF = t'.bodyNF)
    (d : Candidate Ω t.domainNF) (d' : Candidate Ω t'.domainNF)
    (b : t.BodyReads) (b' : t'.BodyReads)
    (hd : Ω.profile t.domainNF ∈ C → d.val = d'.val)
    (hb : ∀ n hn p hp, Ω.profile (t.targetNF n) ∈ C →
        (b n hn p hp).val = (b' n (hD ▸ hn) p (hD ▸ hp)).val) :
    (t.candidate d b).val = (t'.candidate d' b').val := by
  change Candidates.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b) =
    Candidates.ProductTest Ω t'.domainNF t'.bodyNF (t'.testers d') (t'.fibers b')
  rw [testers_eq hD d d' hd,fibers_eq hD hE b b' hb,hD,hE]
end ProductInstance

abbrev Evaluator (Γ : List (Expr S)) (M T : Expr S) :=
  ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno M T e

/-- The exact three uniform finite-bound assertions, expressed without
identifying dependent candidate/value indices by extra axioms. -/
structure Uniform {Γ : List (Expr S)} {M T : Expr S}
    (ev : Evaluator (hw := hw) Ω C hno Γ M T) (F : Nat → Nat) : Prop where
  growth : ∀ k, k+1 ≤ F k
  bounded : ∀ k e, e.Bounded k → Parameter.Bounded Ω C hno (F k) (ev e).parameter
  compare : ∀ k e f, e.Bounded k → f.Bounded k → e.LevelEq (F k) f →
    Parameter.LevelEq Ω C hno k (ev e).parameter (ev f).parameter ∧ (ev e).read.val = (ev f).read.val

namespace Uniform
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
variable {ev : Evaluator (hw := hw) Ω C hno Γ M T} {F : Nat → Nat}
theorem val_bounded (h : Uniform Ω C hno ev F) (k : Nat) (e : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    RawValue.Bounded Ω C hno (F k) ((ev e).val ha).val :=
  (ev e).val_bounded (h.bounded k e he) ha

theorem val_level (h : Uniform Ω C hno ev F) (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (F k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k ((ev e).val ha).val ((ev f).val hb).val :=
  (ev e).val_level (ev f) (h.compare k e f he hf hef).1 ha hb
end Uniform

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
theorem lookup_parameter {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : Converts T A) (e : Environment (hw := hw) Ω C hno Γ) :
    (lookup h hd hc e).parameter = e.parameters n := by
  have ht := e.type_convert_eq h (HasType.lookup h.valid hd) hc
  have hp := e.lawful n A hd
  rw [← ht] at hp
  by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
  · rw [parameter_eq _ ha]
    exact hp.value_spec ha
  · rw [show (lookup h hd hc e).parameter = none from dite_eq_right ha]
    cases hh : e.parameters n with
    | none => rfl
    | some v =>
      rw [hh] at hp
      exact False.elim (ha hp.active)

theorem lookup_uniform {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : Converts T A) :
    Uniform (hw := hw) Ω C hno (lookup h hd hc) (fun k => k+1) := by
  constructor
  · intro k; exact le_refl _
  · intro k e he
    rw [lookup_parameter]
    exact Parameter.bounded_mono (Nat.le_succ k) (he n h.scope.1)
  · intro k e f he hf hef
    have hparam : Parameter.LevelEq Ω C hno k (lookup h hd hc e).parameter (lookup h hd hc f).parameter := by
      rw [lookup_parameter,lookup_parameter]
      exact Parameter.level_mono (Nat.le_succ k) (hef.2 n h.scope.1)
    refine ⟨hparam,?_⟩
    apply baseRead_level h hef.1
    intro ha hb
    exact val_level _ _ hparam ha hb

theorem sort_uniform {s t : S} (h : HasType P Γ (.sort s) T)
    (ha : P.axioms s t) (hc : Converts T (.sort t)) :
    Uniform (hw := hw) Ω C hno (sort h ha hc) (fun k => k+1) := by
  constructor
  · intro k; exact le_refl _
  · intro k e _
    apply parameter_bounded
    intro ht
    exact RawValue.bounded_mono (Nat.succ_le_succ (Nat.zero_le k)) (distinguished_bounded Ω C hno _)
  · intro k e f _ _ hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      intro ht ht'
      have hh : e.activeType h ht = f.activeType h ht' := ActiveType.ext (e.actual_type_eq hef.1 h)
      change RawValue.LevelEq Ω C hno k (distinguished Ω C hno (e.activeType h ht)).val
        (distinguished Ω C hno (f.activeType h ht')).val
      rw [hh]
      exact RawValue.level_refl k _
    · exact congrArg (Candidates.Top Ω) (e.actual_expr_eq hef.1 h)
theorem abstractionAction_bounded {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) (k : Nat) (e : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    ActionBound Ω C hno (e.activeType h ha) k (B k) (abstractionAction h hp hc eb e ha) := by
  intro a p hp' hbp
  dsimp only [abstractionAction]
  apply hb.val_bounded
  dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
  exact Environment.bounded_cons _ _ _ _ he hbp

theorem abstractionAction_level {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (B k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (a' : FrameKey Ω C (f.activeType h ha'))
    (hq : a.argument = a'.argument)
    (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp' : PayloadFits Ω C hno a.domain p) (hp'' : PayloadFits Ω C hno a'.domain p')
    (hbp : Parameter.Bounded Ω C hno k p) (hbp' : Parameter.Bounded Ω C hno k p')
    (hpp : Parameter.LevelEq Ω C hno (B k) p p') :
    RawValue.LevelEq Ω C hno k (abstractionAction h hp hc eb e ha a p hp').val
      (abstractionAction h hp hc eb f ha' a' p' hp'').val := by
  dsimp only [abstractionAction]
  apply hb.val_level
  · dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
    exact Environment.bounded_cons _ _ _ _ he hbp
  · dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
    exact Environment.bounded_cons _ _ _ _ hf hbp'
  · dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
    apply Environment.level_cons hef
    · exact hq ▸ .refl _
    · exact hpp

theorem abstraction_val_level {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (B k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k ((abstraction h hp hc eb e).val ha).val
      ((abstraction h hp hc eb f).val ha').val := by
  apply lambdaValue_level_of_type_eq Ω C hno (e.actual_type_eq hef.1 h)
  exact abstractionAction_level h hp hc eb hb k e f he hf hef ha ha'

theorem abstraction_uniform {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) :
    Uniform Ω C hno (abstraction h hp hc eb) (fun k => B k + 1) := by
  constructor
  · intro k
    exact le_trans (hb.growth k) (Nat.le_succ _)
  · intro k e he
    apply parameter_bounded
    intro ha
    apply lambdaValue_bounded Ω C hno (by have := hb.growth k; omega)
    · exact abstractionAction_bounded h hp hc eb hb k e he ha
    · intro a p p' hp' hp'' hbp hbp' hpp
      exact abstractionAction_level h hp hc eb hb k e e he he (e.level_refl _) ha ha
        a a rfl p p' hp' hp'' hbp hbp' hpp
  · intro k e f he hf hef
    have hf' := e.level_mono (Nat.le_succ (B k)) hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      exact abstraction_val_level h hp hc eb hb k e f he hf hf'
    · apply baseRead_level h hef.1
      exact abstraction_val_level h hp hc eb hb k e f he hf hf'

def appBound (F N : Nat → Nat) (k : Nat) : Nat :=
  1 + max (max (max k (F k)) (N k)) (max (F (max k (N k))) (N (max k (F k))))

 theorem applicationValue_bounded {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E)) (en : Evaluator (hw := hw) Ω C hno Γ n D)
    {F N : Nat → Nat} (huf : Uniform Ω C hno ef F) (_hun : Uniform Ω C hno en N)
    (k : Nat) (e : Environment (hw := hw) Ω C hno Γ) (he : e.Bounded k)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    RawValue.Bounded Ω C hno (appBound F N k) (applicationValue h hf hn hc ef en e ha).val := by
  dsimp only [applicationValue]
  split
  ·
    apply RawValue.bounded_mono (m := appBound F N k) (n := F k) (by unfold appBound; omega)
    apply applyValue_bounded
    exact huf.val_bounded k e he _
  · exact RawValue.bounded_mono (by unfold appBound; omega) (distinguished_bounded Ω C hno _)

 theorem applicationValue_level {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E)) (en : Evaluator (hw := hw) Ω C hno Γ n D)
    {F N : Nat → Nat} (huf : Uniform Ω C hno ef F) (hun : Uniform Ω C hno en N)
    (k : Nat) (e e' : Environment (hw := hw) Ω C hno Γ) (he : e.Bounded k) (he' : e'.Bounded k)
    (hee : e.LevelEq (appBound F N k) e')
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst e'.images).normalForm)) :
    RawValue.LevelEq Ω C hno k (applicationValue h hf hn hc ef en e ha).val
      (applicationValue h hf hn hc ef en e' ha').val := by
  have ht := e.actual_type_eq hee.1 hf
  by_cases hF : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm)
  · have hF' : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e'.images).normalForm) := ht ▸ hF
    simp only [applicationValue, hF, hF', dite_true]
    apply applyValue_level_of_type_eq Ω C hno (j := F k) (r := N k) ht
    · exact huf.val_bounded k e he _
    · exact huf.val_level (max k (N k)) e e'
        (e.bounded_mono (le_max_left _ _) he) (e'.bounded_mono (le_max_left _ _) he')
        (e.level_mono (by unfold appBound; omega) hee) _ _
    · exact e.actual_expr_eq hee.1 hn
    · exact hun.bounded k e he
    · apply Parameter.level_mono (le_max_right k (F k))
      exact (hun.compare (max k (F k)) e e'
        (e.bounded_mono (le_max_left _ _) he) (e'.bounded_mono (le_max_left _ _) he')
        (e.level_mono (by unfold appBound; omega) hee)).1
  · have hF' : ¬ ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e'.images).normalForm) := ht ▸ hF
    simp only [applicationValue, hF, hF', dite_false]
    have hA : e.activeType h ha = e'.activeType h ha' := ActiveType.ext (e.actual_type_eq hee.1 h)
    have hv := congrArg (fun A : ActiveType Ω C => (distinguished (hw := hw) Ω C hno A).val) hA
    rw [hv]
    exact RawValue.level_refl k _

 theorem application_uniform {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E)) (en : Evaluator (hw := hw) Ω C hno Γ n D)
    {F N : Nat → Nat} (huf : Uniform Ω C hno ef F) (hun : Uniform Ω C hno en N) :
    Uniform Ω C hno (application h hf hn hc ef en) (appBound F N) := by
  constructor
  · intro k; unfold appBound; omega
  · intro k e he
    apply parameter_bounded
    exact applicationValue_bounded h hf hn hc ef en huf hun k e he
  · intro k e e' he he' hee
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hee.1 h)
      exact applicationValue_level h hf hn hc ef en huf hun k e e' he he' hee
    · apply baseRead_level h hee.1
      exact applicationValue_level h hf hn hc ef en huf hun k e e' he he' hee

end PreResult

omit [Fintype S] in
theorem Base.update_congr {T U : ActualType Ω} (b : Base Ω) (hTU : T = U)
    (d : Candidate Ω T.val) (e : Candidate Ω U.val) (hde : d.val = e.val) :
    Base.update Ω b T d = Base.update Ω b U e := by
  subst U
  have hd : d = e := Subtype.ext hde
  subst e
  rfl

theorem withBase_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type)
    {b b' : Base Ω} (hbb : b = b') (k : Nat) :
    RawValue.LevelEq (hw := hw) Ω C hno k (withBase Ω C hno T b).val (withBase Ω C hno U b').val := by
  have ht := ActiveType.ext hTU
  subst U
  subst b'
  exact RawValue.level_refl k _

theorem distinguished_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type) (k : Nat) :
    RawValue.LevelEq (hw := hw) Ω C hno k (distinguished Ω C hno T).val (distinguished Ω C hno U).val := by
  have ht := ActiveType.ext hTU
  subst U
  exact RawValue.level_refl k _

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
def productBound (D B : Nat → Nat) (k : Nat) : Nat := 1 + max k (max (D k) (B k))

theorem productCandidate_level {D E : Expr S} {a b c : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (hC : IsComponent (PrimaryEdge P) C)
    {F B : Nat → Nat} (hud : Uniform Ω C hno ed F) (hub : Uniform Ω C hno eb B)
    (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (productBound F B k) f)
    (hK : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd hb hr ed eb f).val := by
  let t := productData hd hb hr e
  let u := productData hd hb hr f
  have hp := e.actual_expr_eq hef.1 (HasType.product hd hb hr)
  have hdu := Expr.pi.inj ((t.product_nf.symm.trans hp).trans u.product_nf)
  have hk : Ω.profile (.pi t.domainNF t.bodyNF) ∈ C := t.product_nf ▸ hK
  apply ProductInstance.candidate_eq hdu.1 hdu.2
  · intro _
    exact (hud.compare k e f he hf (e.level_mono (by unfold productBound; omega) hef)).2
  · intro n hn p hpn hc
    have hnb := t.domain_not_minus hC hn hk hc
    have hbp : Parameter.Bounded Ω C hno k p := Parameter.bounded_of_not_minus hnb hpn
    apply (hub.compare k (t.extend hn p hpn) (u.extend (hdu.1 ▸ hn) p (hdu.1 ▸ hpn)) ?_ ?_ ?_).2
    · dsimp only [ProductInstance.extend]
      exact Environment.bounded_cons _ _ _ _ he hbp
    · dsimp only [ProductInstance.extend]
      exact Environment.bounded_cons _ _ _ _ hf hbp
    · dsimp only [ProductInstance.extend]
      apply Environment.level_cons (e.level_mono (by unfold productBound; omega) hef)
      · exact .refl _
      · exact Parameter.level_refl _ _

theorem product_val_level {D E : Expr S} {a b c : S} (h : HasType P Γ (.pi D E) T)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hc : Converts T (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (hC : IsComponent (PrimaryEdge P) C)
    {F B : Nat → Nat} (hud : Uniform Ω C hno ed F) (hub : Uniform Ω C hno eb B)
    (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (productBound F B k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k ((product h hd hb hr hc ed eb e).val ha).val
      ((product h hd hb hr hc ed eb f).val ha').val := by
  have hp := e.actual_expr_eq hef.1 h
  have ht := e.actual_type_eq hef.1 h
  by_cases hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
  · have hh' : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∈ C := hp ▸ hh
    simp only [product,hh,hh']
    apply withBase_level_of_type_eq Ω C hno ht
    apply Base.update_congr Ω _ (Subtype.ext hp)
    exact productCandidate_level hd hb hr ed eb hC hud hub k e f he hf hef hh.2
  · have hh' : ¬ (({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∈ C) := hp ▸ hh
    simp only [product,hh,hh',dite_false]
    exact distinguished_level_of_type_eq Ω C hno ht k

theorem product_uniform {D E : Expr S} {a b c : S} (h : HasType P Γ (.pi D E) T)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hc : Converts T (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (hC : IsComponent (PrimaryEdge P) C)
    {F B : Nat → Nat} (hud : Uniform Ω C hno ed F) (hub : Uniform Ω C hno eb B) :
    Uniform Ω C hno (product h hd hb hr hc ed eb) (productBound F B) := by
  constructor
  · intro k; unfold productBound; omega
  · intro k e _
    apply parameter_bounded
    intro ha
    dsimp only [product]
    split
    · exact RawValue.bounded_mono (by unfold productBound; omega) (withBase_bounded Ω C hno _ _)
    · exact RawValue.bounded_mono (by unfold productBound; omega) (distinguished_bounded Ω C hno _)
  · intro k e f he hf hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      exact product_val_level h hd hb hr hc ed eb hC hud hub k e f he hf hef
    · have hp := e.actual_expr_eq hef.1 h
      by_cases hh : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
      · have hh' : Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∈ C := hp ▸ hh
        simp only [product,hh,hh',ite_true]
        exact productCandidate_level hd hb hr ed eb hC hud hub k e f he hf hef hh
      · have hh' : Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∉ C := hp ▸ hh
        simp only [product,hh,hh',ite_false]
        exact congrArg (Candidates.Top Ω) hp
end PreResult
end

universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- The manuscript's finite-bound lemma for every stored typing tree. No
normalization or candidate restriction is imposed on the raw environment. -/
theorem preEvaluate_uniform {Γ : List (Expr S)} {M T : Expr S}
    (hC : IsComponent (PrimaryEdge P) C) (t : TypingTree P Γ M T) :
    ∃ F, Uniform (hw := hw) Ω C hno (preEvaluate Ω C hno t) F := by
  induction t with
  | var h hd hc => exact ⟨_,PreResult.lookup_uniform h hd hc⟩
  | sort h ha hc => exact ⟨_,PreResult.sort_uniform h ha hc⟩
  | product h d b hr hc ihd ihb =>
    obtain ⟨F,hF⟩ := ihd
    obtain ⟨B,hB⟩ := ihb
    exact ⟨_,PreResult.product_uniform h d.typing b.typing hr hc _ _ hC hF hB⟩
  | abstraction h d b hp hc _ ihb =>
    obtain ⟨B,hB⟩ := ihb
    exact ⟨_,PreResult.abstraction_uniform h hp hc _ hB⟩
  | application h f a hc ihf iha =>
    obtain ⟨F,hF⟩ := ihf
    obtain ⟨N,hN⟩ := iha
    exact ⟨_,PreResult.application_uniform h f.typing a.typing hc _ _ hF hN⟩

namespace RawValue
variable {Ω C hno}
theorem all_levels_eq {v w : RawValue (hw := hw) Ω C hno}
    (h : ∀ n, LevelEq Ω C hno n v w) : v = w := by
  cases v <;> cases w <;> try exact False.elim (h 0)
  · exact congrArg _ (h 0)
  · exact congrArg _ (FreeObservations.Agree.all_levels_eq h)
  · exact congrArg _ (h 0)
end RawValue
namespace Parameter
variable {Ω C hno}
theorem all_levels_eq {v w : Option (RawValue (hw := hw) Ω C hno)}
    (h : ∀ n, LevelEq Ω C hno n v w) : v = w := by
  cases v <;> cases w <;> try exact False.elim (h 0)
  · rfl
  · exact congrArg some (RawValue.all_levels_eq h)
end Parameter

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}
def Compatible (e f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  e.ImageCompatible f ∧ ∀ n, n < Γ.length → e.parameters n = f.parameters n

theorem Compatible.level {e f : Environment (hw := hw) Ω C hno Γ}
    (h : e.Compatible f) (k : Nat) : e.LevelEq k f := by
  refine ⟨h.1, fun n hn => ?_⟩
  rw [h.2 n hn]
  exact Parameter.level_refl _ _
end Environment

namespace Uniform
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
variable {ev : Evaluator (hw := hw) Ω C hno Γ M T} {F : Nat → Nat}
theorem compatible (h : Uniform Ω C hno ev F)
    (e f : Environment (hw := hw) Ω C hno Γ) (hef : e.Compatible f) :
    (ev e).parameter = (ev f).parameter ∧ (ev e).read.val = (ev f).read.val := by
  obtain ⟨i,hi⟩ := e.exists_bound
  obtain ⟨j,hj⟩ := f.exists_bound
  have hc (k : Nat) := h.compare (max k (max i j)) e f
    (e.bounded_mono (by omega) hi) (f.bounded_mono (by omega) hj)
    (hef.level _)
  constructor
  · apply Parameter.all_levels_eq
    intro k
    exact Parameter.level_mono (le_max_left _ _) (hc k).1
  · exact (hc 0).2
end Uniform

/-- Compatible-image invariance, including arbitrary raw non-SN images. -/
theorem preEvaluate_compatible {Γ : List (Expr S)} {M T : Expr S}
    (hC : IsComponent (PrimaryEdge P) C) (t : TypingTree P Γ M T)
    (e f : Environment (hw := hw) Ω C hno Γ) (hef : e.Compatible f) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t f).read.val := by
  obtain ⟨F,hF⟩ := preEvaluate_uniform Ω C hno hC t
  exact hF.compatible e f hef

end PureTypeSystem.ObservationValues

end OAI
