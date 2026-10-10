import OAI.GroupTheory.RightAngledArtin.ResidualFiniteness
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-! Signed trace normal forms and slowly varying barycentric directions. -/

namespace TraceWords

variable {V : Type*} (L : SimpleGraph V)
abbrev Letter (V : Type*) := V × Bool
abbrev Word (V : Type*) := List (Letter V)

def invLetter (x : Letter V) : Letter V := (x.1, !x.2)
@[simp] theorem invLetter_invLetter (x : Letter V) : invLetter (invLetter x) = x := by
  cases x; simp [invLetter]

def Independent (x y : Letter V) : Prop := L.Adj x.1 y.1
@[simp] theorem independent_inv_left (x y : Letter V) :
    Independent L (invLetter x) y ↔ Independent L x y := Iff.rfl
@[simp] theorem independent_inv_right (x y : Letter V) :
    Independent L x (invLetter y) ↔ Independent L x y := Iff.rfl
@[simp] theorem independent_self (x : Letter V) : ¬ Independent L x x := fun h => L.irrefl h
theorem Independent.symm {x y : Letter V} (h : Independent L x y) : Independent L y x :=
  L.symm.symm _ _ h

/-- A single exchange of independent neighboring occurrences. -/
inductive Swap : Word V → Word V → Prop
  | head {x y : Letter V} {w : Word V} (h : Independent L x y) :
      Swap (x :: y :: w) (y :: x :: w)
  | cons (x : Letter V) {w w' : Word V} (h : Swap w w') : Swap (x :: w) (x :: w')

variable {L}
theorem Swap.symm {w w' : Word V} (h : Swap L w w') : Swap L w' w := by
  induction h with
  | head h => exact .head h.symm
  | cons x _ ih => exact .cons x ih

theorem Swap.length {w w' : Word V} (h : Swap L w w') : w.length = w'.length := by
  induction h <;> simp_all

variable (L)
abbrev Equivalent := Relation.EqvGen (Swap L)

variable {L}
@[refl] theorem Equivalent.refl (w : Word V) : Equivalent L w w := Relation.EqvGen.refl _
@[symm] theorem Equivalent.symm {w w' : Word V} (h : Equivalent L w w') :
    Equivalent L w' w := Relation.EqvGen.symm _ _ h
@[trans] theorem Equivalent.trans {w w' w'' : Word V} (h : Equivalent L w w')
    (h' : Equivalent L w' w'') : Equivalent L w w'' := Relation.EqvGen.trans _ _ _ h h'

theorem Equivalent.cons (x : Letter V) {w w' : Word V} (h : Equivalent L w w') :
    Equivalent L (x :: w) (x :: w') := by
  induction h with
  | rel _ _ h => exact .rel _ _ (.cons x h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm ih
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem Equivalent.length {w w' : Word V} (h : Equivalent L w w') : w.length = w'.length := by
  induction h with
  | rel _ _ h => exact h.length
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable (L)
/-- Remove an occurrence accessible from the left through independent letters.
This retains the actual other occurrences, not merely their group value. -/
inductive Extract (x : Letter V) : Word V → Word V → Prop
  | head (w : Word V) : Extract x (x :: w) w
  | cons {y : Letter V} {w w' : Word V} (h : Independent L x y)
      (e : Extract x w w') : Extract x (y :: w) (y :: w')

variable {L}
theorem Extract.length {x : Letter V} {w w' : Word V} (h : Extract L x w w') :
    w'.length + 1 = w.length := by
  induction h <;> simp_all

theorem Extract.equivalent {x : Letter V} {w w' : Word V} (h : Extract L x w w') :
    Equivalent L w (x :: w') := by
  induction h with
  | head => exact .refl _
  | @cons y w w' h e ih =>
      exact (ih.cons y).trans (.rel _ _ (.head h.symm))

theorem Extract.unique {x : Letter V} {w v v' : Word V}
    (h : Extract L x w v) (h' : Extract L x w v') : v = v' := by
  induction h generalizing v' with
  | head w =>
      cases h' with
      | head => rfl
      | cons hi _ => exact False.elim (independent_self L x hi)
  | @cons y w v hi he ih =>
      cases h' with
      | head => exact False.elim (independent_self L x hi)
      | cons _ he' => exact congrArg (List.cons y) (ih he')

/-- Independent accessible occurrences may be removed in either order. -/
theorem Extract.diamond {x y : Letter V} {w v u : Word V}
    (hxy : Independent L x y) (hx : Extract L x w v) (hy : Extract L y w u) :
    ∃ t, Extract L y v t ∧ Extract L x u t := by
  induction hx generalizing u with
  | head w =>
      cases hy with
      | head => exact False.elim (independent_self L x hxy)
      | cons _ he => exact ⟨_,he,.head _⟩
  | @cons a w v hxa hx ih =>
      cases hy with
      | head => exact ⟨_,.head _,hx⟩
      | cons hya hy =>
          obtain ⟨t,ht,h't⟩ := ih hy
          exact ⟨a :: t,.cons hya ht,.cons hxa h't⟩

/-- An adjacent commutation does not destroy accessible occurrences. -/
theorem Extract.swap {x : Letter V} {w w' v : Word V}
    (hs : Swap L w w') (he : Extract L x w v) :
    ∃ v', Extract L x w' v' ∧ Equivalent L v v' := by
  induction hs generalizing v with
  | @head a b w hab =>
      cases he with
      | head => exact ⟨_,.cons hab (.head _),.refl _⟩
      | cons hxa he =>
          cases he with
          | head => exact ⟨_,.head _,.refl _⟩
          | cons hxb he =>
              exact ⟨_,.cons hxb (.cons hxa he),.rel _ _ (.head hab)⟩
  | @cons a w w' hs ih =>
      cases he with
      | head => exact ⟨_,.head _,.rel _ _ hs⟩
      | cons hxa he =>
          obtain ⟨v',he',hv'⟩ := ih he
          exact ⟨_,.cons hxa he',hv'.cons a⟩

variable (L)
/-- Delete an inverse pair after commuting its endpoints together. -/
inductive Step : Word V → Word V → Prop
  | head {x : Letter V} {w w' : Word V} (h : Extract L (invLetter x) w w') :
      Step (x :: w) w'
  | cons (x : Letter V) {w w' : Word V} (h : Step w w') : Step (x :: w) (x :: w')

variable {L}
theorem Step.length {w w' : Word V} (h : Step L w w') : w'.length + 2 = w.length := by
  induction h with
  | head h => have := h.length; simp only [List.length_cons]; omega
  | cons _ _ ih => simp_all

/-- Lift a cancellation across one independent exchange, tracking its output. -/
theorem Step.swap {w w' v : Word V} (hs : Swap L w w') (he : Step L w v) :
    ∃ v', Step L w' v' ∧ Equivalent L v v' := by
  induction hs generalizing v with
  | @head a b w hab =>
      cases he with
      | head he =>
          cases he with
          | head => exact False.elim (independent_self L a hab)
          | cons _ he => exact ⟨_,.cons b (.head he),.refl _⟩
      | cons _ he =>
          cases he with
          | head he => exact ⟨_,.head (.cons hab.symm he),.refl _⟩
          | cons _ he => exact ⟨_,.cons b (.cons a he),.rel _ _ (.head hab)⟩
  | @cons a w w' hs ih =>
      cases he with
      | head he =>
          obtain ⟨v',he',hv'⟩ := he.swap hs
          exact ⟨_,.head he',hv'⟩
      | cons _ he =>
          obtain ⟨v',he',hv'⟩ := ih he
          exact ⟨_,.cons a he',hv'.cons a⟩

/-- The only overlapping cancellation shares the accessible occurrence.
Its two outcomes differ only by exchanges; disjoint deletions commute. -/
theorem Extract.step {x : Letter V} {w v u : Word V}
    (hx : Extract L x w v) (hs : Step L w u) :
    Equivalent L v (invLetter x :: u) ∨
      ∃ t, Step L v t ∧ Extract L x u t := by
  induction hx generalizing u with
  | head w =>
      cases hs with
      | head he => exact Or.inl he.equivalent
      | cons _ hs => exact Or.inr ⟨_,hs,.head _⟩
  | @cons a w v hxa hx ih =>
      cases hs with
      | head he =>
          obtain ⟨t,ht,h't⟩ := hx.diamond (show Independent L x (invLetter a) from hxa) he
          exact Or.inr ⟨t,.head ht,h't⟩
      | cons _ hs =>
          rcases ih hs with h | ⟨t,ht,h't⟩
          · exact Or.inl ((h.cons a).trans (.rel _ _ (.head hxa.symm)))
          · exact Or.inr ⟨a :: t,.cons a ht,.cons hxa h't⟩

/-- Local confluence modulo independent exchanges. -/
theorem Step.diamond {w v u : Word V} (hv : Step L w v) (hu : Step L w u) :
    Equivalent L v u ∨ ∃ t t', Step L v t ∧ Step L u t' ∧ Equivalent L t t' := by
  induction hv generalizing u with
  | @head x w v he =>
      cases hu with
      | head he' => exact Or.inl (he.unique he' ▸ .refl _)
      | cons _ hu =>
          rcases he.step hu with h | ⟨t,ht,h't⟩
          · exact Or.inl (by simpa using h)
          · exact Or.inr ⟨t,t,ht,.head h't,.refl _⟩
  | @cons x w v hv ih =>
      cases hu with
      | head he =>
          rcases he.step hv with h | ⟨t,ht,h't⟩
          · exact Or.inl (by simpa using h.symm)
          · exact Or.inr ⟨t,t,.head h't,ht,.refl _⟩
      | cons _ hu =>
          rcases ih hu with h | ⟨t,t',ht,h't,htt'⟩
          · exact Or.inl (h.cons x)
          · exact Or.inr ⟨x :: t,x :: t',.cons x ht,.cons x h't,htt'.cons x⟩

instance : Std.Symm (Swap L) where
  symm _ _ h := h.symm

theorem Equivalent.step {w w' v : Word V} (hs : Equivalent L w w') (he : Step L w v) :
    ∃ v', Step L w' v' ∧ Equivalent L v v' := by
  have hh : Relation.ReflTransGen (Swap L) w w' := by
    rwa [← Relation.EqvGen.eqvGen_eq_reflTransGen]
  clear hs
  induction hh with
  | refl => exact ⟨_,he,.refl _⟩
  | tail _ hs ih =>
      obtain ⟨v',he',hv'⟩ := ih
      obtain ⟨v'',he'',hv''⟩ := he'.swap hs
      exact ⟨_,he'',hv'.trans hv''⟩

variable (L)
def traceSetoid : Setoid (Word V) where
  r := Equivalent L
  iseqv := ⟨Equivalent.refl,Equivalent.symm,Equivalent.trans⟩

abbrev Trace := Quotient (traceSetoid L)
def ofWord (w : Word V) : Trace L := Quotient.mk _ w

def traceLength : Trace L → ℕ := Quotient.lift List.length (fun _ _ h => h.length)
@[simp] theorem traceLength_ofWord (w : Word V) : traceLength L (ofWord L w) = w.length := rfl

@[simp] theorem ofWord_eq {w v : Word V} : ofWord L w = ofWord L v ↔ Equivalent L w v :=
  Quotient.eq

/-- Reduction of traces, not a choice of ordered representative. -/
def ReductionStep (t t' : Trace L) : Prop :=
  ∃ w v, Step L w v ∧ ofWord L w = t ∧ ofWord L v = t'

variable {L}
theorem Step.trace {w v : Word V} (h : Step L w v) :
    ReductionStep L (ofWord L w) (ofWord L v) := ⟨w,v,h,rfl,rfl⟩

theorem ReductionStep.representative {w : Word V} {t : Trace L}
    (h : ReductionStep L (ofWord L w) t) :
    ∃ v, Step L w v ∧ ofWord L v = t := by
  obtain ⟨a,b,hab,ha,hb⟩ := h
  obtain ⟨v,hv,hbv⟩ := ((ofWord_eq L).mp ha).step hab
  exact ⟨v,hv,((ofWord_eq L).mpr hbv).symm.trans hb⟩

theorem ReductionStep.length {t t' : Trace L} (h : ReductionStep L t t') :
    traceLength L t' + 2 = traceLength L t := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  exact h.length

theorem ReductionStep.diamond {t t' t'' : Trace L}
    (h : ReductionStep L t t') (h' : ReductionStep L t t'') :
    t' = t'' ∨ ∃ u, ReductionStep L t' u ∧ ReductionStep L t'' u := by
  induction t using Quotient.inductionOn with
  | h w =>
      obtain ⟨v,hv,rfl⟩ := h.representative
      obtain ⟨u,hu,rfl⟩ := h'.representative
      rcases hv.diamond hu with he | ⟨a,b,ha,hb,hab⟩
      · exact Or.inl ((ofWord_eq L).mpr he)
      · refine Or.inr ⟨ofWord L a,ha.trace,?_⟩
        rw [(ofWord_eq L).mpr hab]
        exact hb.trace

variable (L)
abbrev Reduction := Relation.ReflTransGen (ReductionStep L)
def Reduced (t : Trace L) : Prop := ∀ t', ¬ ReductionStep L t t'

variable {L}
theorem Reduction.length_le {t t' : Trace L} (h : Reduction L t t') :
    traceLength L t' ≤ traceLength L t := by
  induction h with
  | refl => rfl
  | tail _ hs ih => have := hs.length; omega

theorem Reduction.confluence {t t' t'' : Trace L}
    (h : Reduction L t t') (h' : Reduction L t t'') :
    ∃ u, Reduction L t' u ∧ Reduction L t'' u := by
  apply Relation.church_rosser (r := ReductionStep L) _ h h'
  intro _ _ _ ha hb
  rcases ha.diamond hb with rfl | ⟨u,hu,hu'⟩
  · exact ⟨_,.refl,.refl⟩
  · exact ⟨u,.single hu,.single hu'⟩

theorem Reduced.reduction_eq {t t' : Trace L} (h : Reduced L t) (hr : Reduction L t t') :
    t = t' := by
  rcases hr.cases_head with he | ⟨u,hu,_⟩
  · exact he
  · exact False.elim (h u hu)

theorem exists_reduced (t : Trace L) : ∃ t', Reduction L t t' ∧ Reduced L t' := by
  classical
  induction hn : traceLength L t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      by_cases ht : Reduced L t
      · exact ⟨t,.refl,ht⟩
      · obtain ⟨u,hu⟩ : ∃ u, ReductionStep L t u := by simpa [Reduced] using ht
        have hl := hu.length
        obtain ⟨v,hv,hv'⟩ := ih (traceLength L u) (by omega) u rfl
        exact ⟨v,hv.head hu,hv'⟩

theorem reduced_unique {t u v : Trace L} (hu : Reduction L t u) (hv : Reduction L t v)
    (hru : Reduced L u) (hrv : Reduced L v) : u = v := by
  obtain ⟨a,ha,h'a⟩ := hu.confluence hv
  exact (hru.reduction_eq ha).trans (hrv.reduction_eq h'a).symm

variable (L)
def normalTrace (t : Trace L) : Trace L := (exists_reduced t).choose

theorem normalTrace_reduction (t : Trace L) : Reduction L t (normalTrace L t) :=
  (exists_reduced t).choose_spec.1

theorem normalTrace_reduced (t : Trace L) : Reduced L (normalTrace L t) :=
  (exists_reduced t).choose_spec.2

variable {L}
theorem Reduced.normalTrace_eq {t : Trace L} (h : Reduced L t) : normalTrace L t = t :=
  (h.reduction_eq (normalTrace_reduction L t)).symm

theorem Reduction.normalTrace_eq {t u : Trace L} (h : Reduction L t u) :
    normalTrace L t = normalTrace L u :=
  reduced_unique (normalTrace_reduction L t) (h.trans (normalTrace_reduction L u))
    (normalTrace_reduced L t) (normalTrace_reduced L u)

@[simp] theorem normalTrace_idem (t : Trace L) :
    normalTrace L (normalTrace L t) = normalTrace L t :=
  (normalTrace_reduced L t).normalTrace_eq

theorem Swap.append_right {w v : Word V} (h : Swap L w v) (u : Word V) :
    Swap L (w ++ u) (v ++ u) := by
  induction h with
  | head h => exact .head h
  | cons x _ ih => exact .cons x ih

theorem Equivalent.append_right {w v : Word V} (h : Equivalent L w v) (u : Word V) :
    Equivalent L (w ++ u) (v ++ u) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.append_right u)
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem Equivalent.append_left {w v : Word V} (h : Equivalent L w v) (u : Word V) :
    Equivalent L (u ++ w) (u ++ v) := by
  induction u with
  | nil => exact h
  | cons a u ih => exact ih.cons a

theorem Extract.append_right {x : Letter V} {w v : Word V}
    (h : Extract L x w v) (u : Word V) : Extract L x (w ++ u) (v ++ u) := by
  induction h with
  | head => exact .head _
  | cons hi _ ih => exact .cons hi ih

theorem Step.append_right {w v : Word V} (h : Step L w v) (u : Word V) :
    Step L (w ++ u) (v ++ u) := by
  induction h with
  | head h => exact .head (h.append_right u)
  | cons x _ ih => exact .cons x ih

theorem Step.append_left {w v : Word V} (h : Step L w v) (u : Word V) :
    Step L (u ++ w) (u ++ v) := by
  induction u with
  | nil => exact h
  | cons a u ih => exact .cons a ih

variable (L)
def appendTrace (t u : Trace L) : Trace L :=
  Quotient.liftOn₂ t u (fun w v => ofWord L (w ++ v)) (by
    intro w v w' v' hw hv
    exact (ofWord_eq L).mpr ((hw.append_right v).trans (hv.append_left w')))

@[simp] theorem appendTrace_ofWord (w v : Word V) :
    appendTrace L (ofWord L w) (ofWord L v) = ofWord L (w ++ v) := rfl

variable {L}
theorem ReductionStep.append_left {t t' : Trace L} (h : ReductionStep L t t') (u : Trace L) :
    ReductionStep L (appendTrace L u t) (appendTrace L u t') := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  induction u using Quotient.inductionOn with
  | h a => exact (h.append_left a).trace

theorem ReductionStep.append_right {t t' : Trace L} (h : ReductionStep L t t') (u : Trace L) :
    ReductionStep L (appendTrace L t u) (appendTrace L t' u) := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  induction u using Quotient.inductionOn with
  | h a => exact (h.append_right a).trace

theorem Reduction.append_left {t t' : Trace L} (h : Reduction L t t') (u : Trace L) :
    Reduction L (appendTrace L u t) (appendTrace L u t') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.append_left u)

theorem Reduction.append_right {t t' : Trace L} (h : Reduction L t t') (u : Trace L) :
    Reduction L (appendTrace L t u) (appendTrace L t' u) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.append_right u)

theorem normalTrace_append (t u : Trace L) :
    normalTrace L (appendTrace L t u) =
      normalTrace L (appendTrace L (normalTrace L t) (normalTrace L u)) :=
  Reduction.normalTrace_eq (((normalTrace_reduction L t).append_right u).trans
    ((normalTrace_reduction L u).append_left (normalTrace L t)))

variable (L)
/-- Equality of reduced traces is a monoid congruence on signed words. -/
def normalCon : Con (FreeMonoid (Letter V)) where
  r w v := normalTrace L (ofWord L w.toList) = normalTrace L (ofWord L v.toList)
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h h' => h.trans h'⟩
  mul' {x y z t} hxy hzt := by
    change normalTrace L (appendTrace L (ofWord L x.toList) (ofWord L z.toList)) =
      normalTrace L (appendTrace L (ofWord L y.toList) (ofWord L t.toList))
    calc
      _ = normalTrace L (appendTrace L (normalTrace L (ofWord L x.toList))
        (normalTrace L (ofWord L z.toList))) := normalTrace_append _ _
      _ = normalTrace L (appendTrace L (normalTrace L (ofWord L y.toList))
        (normalTrace L (ofWord L t.toList))) := by rw [hxy,hzt]
      _ = _ := (normalTrace_append _ _).symm

abbrev WordGroup := (normalCon L).Quotient

def groupWord (w : Word V) : WordGroup L := (normalCon L).mk' (FreeMonoid.ofList w)

@[simp] theorem groupWord_nil : groupWord L [] = 1 := rfl
@[simp] theorem groupWord_append (w v : Word V) : groupWord L (w ++ v) =
    groupWord L w * groupWord L v := rfl

@[simp] theorem groupWord_eq {w v : Word V} : groupWord L w = groupWord L v ↔
    normalTrace L (ofWord L w) = normalTrace L (ofWord L v) := Quotient.eq

variable {L}
theorem Step.groupWord {w v : Word V} (h : Step L w v) : groupWord L w = groupWord L v :=
  (groupWord_eq L).mpr (Reduction.normalTrace_eq (Relation.ReflTransGen.single h.trace))

theorem Swap.groupWord {w v : Word V} (h : Swap L w v) : groupWord L w = groupWord L v := by
  apply (groupWord_eq L).mpr
  rw [(ofWord_eq L).mpr (.rel _ _ h)]

theorem isUnit_groupWord_singleton (x : Letter V) : IsUnit (groupWord L [x]) := by
  refine ⟨⟨groupWord L [x],groupWord L [invLetter x],?_,?_⟩,rfl⟩
  · change groupWord L [x,invLetter x] = groupWord L []
    exact (Step.head (.head [])).groupWord
  · change groupWord L [invLetter x,x] = groupWord L []
    exact (Step.head (by simpa using (Extract.head (L := L) (x := invLetter (invLetter x)) []))).groupWord

theorem isUnit_groupWord (w : Word V) : IsUnit (groupWord L w) := by
  induction w with
  | nil => exact isUnit_one
  | cons x w ih =>
      change IsUnit (groupWord L [x] * groupWord L w)
      exact (isUnit_groupWord_singleton x).mul ih

variable (L)
noncomputable instance wordGroupGroup : Group (WordGroup L) := groupOfIsUnit (by
  intro x
  induction x using Con.induction_on with
  | H w => exact isUnit_groupWord w.toList)

@[simp] theorem groupWord_inv_singleton (x : Letter V) :
    groupWord L [invLetter x] = (groupWord L [x])⁻¹ := by
  apply mul_left_cancel (a := groupWord L [x])
  rw [mul_inv_cancel,← groupWord_append]
  exact (Step.head (.head [])).groupWord

section Evaluation
variable {K : Type*} [Group K] (f : V → K)

def letterValue (x : Letter V) : K := if x.2 then f x.1 else (f x.1)⁻¹
@[simp] theorem letterValue_positive (v : V) : letterValue f (v,true) = f v := rfl
@[simp] theorem letterValue_negative (v : V) : letterValue f (v,false) = (f v)⁻¹ := rfl
@[simp] theorem letterValue_inverse (x : Letter V) : letterValue f (invLetter x) =
    (letterValue f x)⁻¹ := by
  rcases x with ⟨x,b⟩; cases b <;> simp [letterValue,invLetter]

def wordEval (w : Word V) : K := (w.map (letterValue f)).prod
@[simp] theorem wordEval_nil : wordEval f [] = 1 := rfl
@[simp] theorem wordEval_cons (x : Letter V) (w : Word V) :
    wordEval f (x :: w) = letterValue f x * wordEval f w := rfl
@[simp] theorem wordEval_append (w v : Word V) :
    wordEval f (w ++ v) = wordEval f w * wordEval f v := by simp [wordEval]
@[simp] theorem wordEval_singleton (x : Letter V) : wordEval f [x] = letterValue f x := by
  simp

variable {L f}
theorem letterValue_commute (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {x y : Letter V} (h : Independent L x y) : Commute (letterValue f x) (letterValue f y) := by
  rcases x with ⟨x,b⟩; rcases y with ⟨y,c⟩
  have hh := hf x y h
  cases b <;> cases c
  · exact hh.inv_left.inv_right
  · exact hh.inv_left
  · exact hh.inv_right
  · exact hh

theorem Swap.wordEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {w v : Word V} (h : Swap L w v) : wordEval f w = wordEval f v := by
  induction h with
  | head h => simp only [wordEval_cons,← mul_assoc,(letterValue_commute hf h).eq]
  | cons _ _ ih => simp only [wordEval_cons,ih]

theorem Equivalent.wordEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {w v : Word V} (h : Equivalent L w v) : wordEval f w = wordEval f v := by
  induction h with
  | rel _ _ h => exact h.wordEval hf
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem Step.wordEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {w v : Word V} (h : Step L w v) : wordEval f w = wordEval f v := by
  induction h with
  | head h =>
      rw [wordEval_cons,h.equivalent.wordEval hf,wordEval_cons,letterValue_inverse,
        mul_inv_cancel_left]
  | cons _ _ ih => simp only [wordEval_cons,ih]

variable (L f)
def traceEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y)) : Trace L → K :=
  Quotient.lift (wordEval f) (fun _ _ h => h.wordEval hf)

@[simp] theorem traceEval_ofWord (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    (w : Word V) : traceEval L f hf (ofWord L w) = wordEval f w := rfl

variable {L f}
theorem ReductionStep.traceEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {t u : Trace L} (h : ReductionStep L t u) : traceEval L f hf t = traceEval L f hf u := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  exact h.wordEval hf

theorem Reduction.traceEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {t u : Trace L} (h : Reduction L t u) : traceEval L f hf t = traceEval L f hf u := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (h.traceEval hf)

theorem traceEval_normalTrace (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    (t : Trace L) : traceEval L f hf (normalTrace L t) = traceEval L f hf t :=
  ((normalTrace_reduction L t).traceEval hf).symm

variable (L f)
def groupEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y)) : WordGroup L →* K :=
  (normalCon L).lift (FreeMonoid.lift (letterValue f)) (by
    intro w v h
    change normalTrace L (ofWord L w.toList) = normalTrace L (ofWord L v.toList) at h
    have hh := congrArg (traceEval L f hf) h
    change FreeMonoid.lift (letterValue f) w = FreeMonoid.lift (letterValue f) v
    simpa only [FreeMonoid.lift_apply,traceEval_normalTrace,traceEval_ofWord,wordEval] using hh)

@[simp] theorem groupEval_word (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    (w : Word V) : groupEval L f hf (groupWord L w) = wordEval f w := by
  change FreeMonoid.lift (letterValue f) (FreeMonoid.ofList w) = wordEval f w
  exact FreeMonoid.lift_ofList _ _

end Evaluation

/-- The kernel presentation is compared with the signed trace group, not with
an assumed normal-form model. -/
def toArtin : WordGroup L →* ArtinGroup L :=
  groupEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)

theorem groupWord_commute {v w : V} (h : L.Adj v w) :
    Commute (groupWord L [(v,true)]) (groupWord L [(w,true)]) := by
  change groupWord L [(v,true),(w,true)] = groupWord L [(w,true),(v,true)]
  exact (Swap.head (L := L) (x := (v,true)) (y := (w,true)) (w := []) h).groupWord

def ofArtin : ArtinGroup L →* WordGroup L :=
  artinLift L (fun v => groupWord L [(v,true)]) (fun _ _ h => groupWord_commute L h)

@[simp] theorem ofArtin_generator (v : V) : ofArtin L (artinGenerator L v) =
    groupWord L [(v,true)] := artinLift_generator _ _ _ _

@[simp] theorem toArtin_word (w : Word V) :
    toArtin L (groupWord L w) = wordEval (artinGenerator L) w := groupEval_word _ _ _ _

@[simp] theorem ofArtin_letter (x : Letter V) :
    ofArtin L (letterValue (artinGenerator L) x) = groupWord L [x] := by
  rcases x with ⟨x,b⟩
  cases b
  · change ofArtin L (artinGenerator L x)⁻¹ = groupWord L [(x,false)]
    rw [map_inv,ofArtin_generator]
    exact (groupWord_inv_singleton L (x,true)).symm
  · exact ofArtin_generator L x

theorem ofArtin_word (w : Word V) :
    ofArtin L (wordEval (artinGenerator L) w) = groupWord L w := by
  induction w with
  | nil => exact (ofArtin L).map_one
  | cons x w ih =>
      rw [wordEval_cons,map_mul,ofArtin_letter,ih]
      rfl

theorem ofArtin_toArtin (g : WordGroup L) : ofArtin L (toArtin L g) = g := by
  induction g using Con.induction_on with
  | H w =>
      change ofArtin L (toArtin L (groupWord L w.toList)) = groupWord L w.toList
      rw [toArtin_word,ofArtin_word]

theorem toArtin_ofArtin (g : ArtinGroup L) : toArtin L (ofArtin L g) = g := by
  have he : (toArtin L).comp (ofArtin L) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro v
    change toArtin L (ofArtin L (artinGenerator L v)) = artinGenerator L v
    rw [ofArtin_generator,toArtin_word,wordEval_singleton,letterValue_positive]
  exact DFunLike.congr_fun he g

/-- The actual presented Artin group equals the word group constructed by
confluence of individual-occurrence cancellations. -/
def artinEquiv : ArtinGroup L ≃* WordGroup L where
  toFun := ofArtin L
  invFun := toArtin L
  left_inv := toArtin_ofArtin L
  right_inv := ofArtin_toArtin L
  map_mul' := (ofArtin L).map_mul

/-- Two words have the same value in the actual Artin group exactly when they
have the same reduced trace. -/
theorem artin_word_eq_iff (w v : Word V) :
    wordEval (artinGenerator L) w = wordEval (artinGenerator L) v ↔
      normalTrace L (ofWord L w) = normalTrace L (ofWord L v) := by
  rw [← groupWord_eq]
  constructor
  · intro h
    simpa only [ofArtin_word] using congrArg (ofArtin L) h
  · intro h
    simpa only [toArtin_word] using congrArg (toArtin L) h

theorem trace_reduced_minimal {w : Word V} (h : Reduced L (ofWord L w))
    {v : Word V} (hv : wordEval (artinGenerator L) w = wordEval (artinGenerator L) v) :
    w.length ≤ v.length := by
  have he := (artin_word_eq_iff L w v).mp hv
  rw [h.normalTrace_eq] at he
  have hl := (normalTrace_reduction L (ofWord L v)).length_le
  rwa [← he] at hl


/-! The occurrence-level normal form is now used to control an actual generator
step. No geometric normal-form or direction-vector assertion is assumed. -/

variable {L}

theorem Reduced.of_equivalent {w v : Word V} (h : Reduced L (ofWord L w))
    (he : Equivalent L w v) : Reduced L (ofWord L v) := by
  rwa [← (ofWord_eq L).mpr he]

theorem Reduced.of_append_left {w v : Word V} (h : Reduced L (ofWord L (w ++ v))) :
    Reduced L (ofWord L v) := by
  intro t ht
  exact h _ (ht.append_left (ofWord L w))

theorem Reduced.of_append_right {w v : Word V} (h : Reduced L (ofWord L (w ++ v))) :
    Reduced L (ofWord L w) := by
  intro t ht
  exact h _ (ht.append_right (ofWord L v))

theorem Reduced.tail {x : Letter V} {w : Word V} (h : Reduced L (ofWord L (x :: w))) :
    Reduced L (ofWord L w) :=
  Reduced.of_append_left (w := [x]) h

theorem Extract.append_singleton {x y : Letter V} {w v : Word V}
    (h : Extract L x (w ++ [y]) v) :
    (∃ v', Extract L x w v' ∧ v = v' ++ [y]) ∨
      (x = y ∧ v = w ∧ ∀ a ∈ w, Independent L x a) := by
  induction w generalizing v with
  | nil =>
      cases h with
      | head => exact Or.inr ⟨rfl,rfl,by simp⟩
      | cons _ he => cases he
  | cons a w ih =>
      cases h with
      | head => exact Or.inl ⟨w,.head _,rfl⟩
      | cons ha he =>
          rcases ih he with ⟨v',hv',rfl⟩ | ⟨hxy,rfl,hw⟩
          · exact Or.inl ⟨a :: v',.cons ha hv',rfl⟩
          · refine Or.inr ⟨hxy,rfl,?_⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact ha
            · exact hw b hb

theorem Extract.last {x : Letter V} {w : Word V}
    (h : ∀ a ∈ w, Independent L x a) : Extract L x (w ++ [x]) w := by
  induction w with
  | nil => exact .head []
  | cons a w ih =>
      exact .cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- A cancellation in a reduced word with one appended occurrence must cancel
that new occurrence. The old inverse occurrence was maximal: it can be moved
all the way to the right by independent exchanges. -/
theorem Step.append_reduced {x : Letter V} {w v : Word V}
    (hw : Reduced L (ofWord L w)) (h : Step L (w ++ [x]) v) :
    Equivalent L w (v ++ [invLetter x]) := by
  induction w generalizing v with
  | nil =>
      cases h with
      | head he => cases he
      | cons _ he => cases he
  | cons a w ih =>
      cases h with
      | head he =>
          rcases he.append_singleton with ⟨v',hv',_⟩ | ⟨hax,hv,hi⟩
          · exact False.elim (hw _ (Step.head hv').trace)
          · subst v
            have hia : ∀ b ∈ w, Independent L a b := hi
            have ha : a = invLetter x := by rw [← hax,invLetter_invLetter]
            rw [← ha]
            exact (Extract.last hia).equivalent.symm
      | cons _ he => exact (ih hw.tail he).cons a

/-- On an actual reduced trace, a generator step either adds a maximal
occurrence or removes a maximal inverse occurrence, with no further reduction. -/
theorem reduced_append_alternative {x : Letter V} {w : Word V}
    (hw : Reduced L (ofWord L w)) :
    Reduced L (ofWord L (w ++ [x])) ∨
      ∃ v, Reduced L (ofWord L v) ∧ Equivalent L w (v ++ [invLetter x]) ∧
        normalTrace L (ofWord L (w ++ [x])) = ofWord L v := by
  classical
  by_cases h : Reduced L (ofWord L (w ++ [x]))
  · exact Or.inl h
  · obtain ⟨t,ht⟩ : ∃ t, ReductionStep L (ofWord L (w ++ [x])) t := by
      simpa only [Reduced,not_forall,not_not] using h
    obtain ⟨v,hv,rfl⟩ := ht.representative
    have he := hv.append_reduced hw
    have hr : Reduced L (ofWord L v) := (hw.of_equivalent he).of_append_right
    exact Or.inr ⟨v,hr,he,(Reduction.normalTrace_eq (Relation.ReflTransGen.single hv.trace)).trans
      hr.normalTrace_eq⟩


section RootCounts
variable [LinearOrder V]
variable (L)

/-- The previously encountered minimal ancestral directions of letters
which are dependent on the next direction. Taking the minimum recursively
computes the first minimal ancestor in the occurrence poset. -/
def predecessorRoots (s : Multiset (V × V)) (v : V) : Finset V := by
  classical
  exact ((s.filter (fun p => ¬ L.Adj p.1 v)).map Prod.snd).toFinset

def nextRoot (s : Multiset (V × V)) (v : V) : V :=
  if h : (predecessorRoots L s v).Nonempty then (predecessorRoots L s v).min' h else v

def rootInsert (s : Multiset (V × V)) (v : V) : Multiset (V × V) :=
  (v,nextRoot L s v) ::ₘ s

/-- Each pair records an occurrence's direction and its assigned minimal
ancestral direction. Signs do not change the occurrence dependency relation. -/
def rootScan (s : Multiset (V × V)) (w : Word V) : Multiset (V × V) :=
  w.foldl (fun s x => rootInsert L s x.1) s

@[simp] theorem rootScan_nil (s : Multiset (V × V)) : rootScan L s [] = s := rfl
@[simp] theorem rootScan_cons (s : Multiset (V × V)) (x : Letter V) (w : Word V) :
    rootScan L s (x :: w) = rootScan L (rootInsert L s x.1) w := rfl

theorem rootScan_append (s : Multiset (V × V)) (w v : Word V) :
    rootScan L s (w ++ v) = rootScan L (rootScan L s w) v := List.foldl_append

variable {L}

theorem mem_predecessorRoots {s : Multiset (V × V)} {v r : V} :
    r ∈ predecessorRoots L s v ↔ ∃ p ∈ s, ¬ L.Adj p.1 v ∧ p.2 = r := by
  classical
  simp only [predecessorRoots,Multiset.mem_toFinset,Multiset.mem_map,Multiset.mem_filter]
  aesop

theorem predecessorRoots_cons_independent (s : Multiset (V × V)) {a v : V}
    (r : V) (h : L.Adj a v) :
    predecessorRoots L ((a,r) ::ₘ s) v = predecessorRoots L s v := by
  classical
  simp [predecessorRoots,h]

theorem nextRoot_cons_independent (s : Multiset (V × V)) {a v : V}
    (r : V) (h : L.Adj a v) :
    nextRoot L ((a,r) ::ₘ s) v = nextRoot L s v := by
  simp only [nextRoot,predecessorRoots_cons_independent s r h]

theorem rootInsert_commute (s : Multiset (V × V)) {v w : V} (h : L.Adj v w) :
    rootInsert L (rootInsert L s v) w = rootInsert L (rootInsert L s w) v := by
  simp only [rootInsert,nextRoot_cons_independent s _ h,
    nextRoot_cons_independent s _ (L.symm.symm _ _ h)]
  exact Multiset.cons_swap _ _ _

theorem Swap.rootScan {w v : Word V} (h : Swap L w v) (s : Multiset (V × V)) :
    rootScan L s w = rootScan L s v := by
  induction h generalizing s with
  | head h => simp only [rootScan_cons,rootInsert_commute s h]
  | cons _ _ ih => exact ih _

theorem Equivalent.rootScan {w v : Word V} (h : Equivalent L w v) (s : Multiset (V × V)) :
    rootScan L s w = rootScan L s v := by
  induction h with
  | rel _ _ h => exact h.rootScan s
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Every assigned root occurs as a minimal occurrence, and the root directions
of the whole state form a clique. These assertions simultaneously express
support in a simplex and permanence of old assignments. -/
def RootInvariant (L : SimpleGraph V) (s : Multiset (V × V)) : Prop :=
  (∀ p ∈ s, (p.2,p.2) ∈ s) ∧
    ∀ p ∈ s, ∀ q ∈ s, p.2 ≠ q.2 → L.Adj p.2 q.2

theorem nextRoot_mem_or_new (s : Multiset (V × V)) (v : V) :
    (∃ p ∈ s, p.2 = nextRoot L s v) ∨
      (nextRoot L s v = v ∧ ∀ p ∈ s, L.Adj p.1 v) := by
  classical
  by_cases h : (predecessorRoots L s v).Nonempty
  · left
    have hm := Finset.min'_mem (predecessorRoots L s v) h
    obtain ⟨p,hp,_,he⟩ := mem_predecessorRoots.mp hm
    exact ⟨p,hp,by simpa only [nextRoot,dite_eq_left h] using he⟩
  · refine Or.inr ⟨by simp [nextRoot,h],?_⟩
    intro p hp
    by_contra hn
    exact h ⟨p.2,mem_predecessorRoots.mpr ⟨p,hp,hn,rfl⟩⟩

theorem RootInvariant.insert {s : Multiset (V × V)} (hs : RootInvariant L s) (v : V) :
    RootInvariant L (rootInsert L s v) := by
  classical
  have hr : (nextRoot L s v,nextRoot L s v) ∈ rootInsert L s v := by
    rcases nextRoot_mem_or_new (L := L) s v with ⟨p,hp,he⟩ | ⟨he,_⟩
    · simp only [rootInsert,Multiset.mem_cons]
      right
      rw [← he]
      exact hs.1 p hp
    · simp [rootInsert,he]
  have ha : ∀ p ∈ s, nextRoot L s v ≠ p.2 → L.Adj (nextRoot L s v) p.2 := by
    intro p hp hne
    rcases nextRoot_mem_or_new (L := L) s v with ⟨q,hq,he⟩ | ⟨he,hv⟩
    · rw [← he] at hne ⊢
      exact hs.2 q hq p hp hne
    · rw [he]
      exact L.symm.symm _ _ (hv (p.2,p.2) (hs.1 p hp))
  constructor
  · intro p hp
    rcases Multiset.mem_cons.mp hp with rfl | hp
    · exact hr
    · exact Multiset.mem_cons.mpr (Or.inr (hs.1 p hp))
  · intro p hp q hq hne
    rcases Multiset.mem_cons.mp hp with rfl | hp
    · rcases Multiset.mem_cons.mp hq with rfl | hq
      · exact False.elim (hne rfl)
      · exact ha q hq hne
    · rcases Multiset.mem_cons.mp hq with rfl | hq
      · exact L.symm.symm _ _ (ha p hp hne.symm)
      · exact hs.2 p hp q hq hne

theorem RootInvariant.scan {s : Multiset (V × V)} (hs : RootInvariant L s) (w : Word V) :
    RootInvariant L (rootScan L s w) := by
  induction w generalizing s with
  | nil => exact hs
  | cons x w ih => exact ih (hs.insert x.1)

theorem rootInvariant_word (w : Word V) : RootInvariant L (rootScan L 0 w) :=
  RootInvariant.scan ⟨by simp,by simp⟩ w

variable (L)
def rootCounts (s : Multiset (V × V)) : V →₀ ℕ :=
  (s.map (fun p => Finsupp.single p.2 1)).sum

def wordCounts (w : Word V) : V →₀ ℕ := rootCounts (rootScan L 0 w)

def traceCounts : Trace L → V →₀ ℕ :=
  Quotient.lift (wordCounts L) (fun _ _ h => congrArg rootCounts (h.rootScan 0))

@[simp] theorem traceCounts_ofWord (w : Word V) :
    traceCounts L (ofWord L w) = wordCounts L w := rfl

omit [LinearOrder V] in
@[simp] theorem rootCounts_cons (p : V × V) (s : Multiset (V × V)) :
    rootCounts (p ::ₘ s) = Finsupp.single p.2 1 + rootCounts s := by
  simp [rootCounts]

omit [LinearOrder V] in
@[simp] theorem rootCounts_zero : rootCounts (0 : Multiset (V × V)) = 0 := by
  simp [rootCounts]

theorem wordCounts_append_singleton (w : Word V) (x : Letter V) :
    wordCounts L (w ++ [x]) = wordCounts L w +
      Finsupp.single (nextRoot L (rootScan L 0 w) x.1) 1 := by
  simp only [wordCounts,rootScan_append,rootScan_cons,rootScan_nil,rootInsert,rootCounts_cons]
  exact add_comm _ _


omit [LinearOrder V] in
 theorem rootCounts_mem_iff (s : Multiset (V × V)) (r : V) :
    rootCounts s r ≠ 0 ↔ ∃ p ∈ s, p.2 = r := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
      by_cases hp : p.2 = r
      · simp [rootCounts_cons,hp]
      · simp [rootCounts_cons,hp,ih]

omit [LinearOrder V] in
 theorem rootCounts_support_clique {s : Multiset (V × V)} (hs : RootInvariant L s) :
    ((rootCounts s).support : Set V).Pairwise L.Adj := by
  intro r hr t ht hne
  obtain ⟨p,hp,hpr⟩ := (rootCounts_mem_iff s r).mp (Finsupp.mem_support_iff.mp hr)
  obtain ⟨q,hq,hqt⟩ := (rootCounts_mem_iff s t).mp (Finsupp.mem_support_iff.mp ht)
  rw [← hpr,← hqt] at hne ⊢
  exact hs.2 p hp q hq hne

theorem wordCounts_support_clique (w : Word V) : ((wordCounts L w).support : Set V).Pairwise L.Adj :=
  rootCounts_support_clique L (rootInvariant_word w)

theorem traceCounts_support_clique (t : Trace L) : ((traceCounts L t).support : Set V).Pairwise L.Adj := by
  induction t using Quotient.inductionOn with
  | h w => exact wordCounts_support_clique L w

omit [LinearOrder V] in
 theorem rootCounts_sum [Fintype V] (s : Multiset (V × V)) :
    ∑ v, rootCounts s v = s.card := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
      simp [rootCounts_cons,Finset.sum_add_distrib,ih,Finsupp.single_apply,add_comm]

theorem rootScan_card (s : Multiset (V × V)) (w : Word V) :
    (rootScan L s w).card = s.card + w.length := by
  induction w generalizing s with
  | nil => simp
  | cons x w ih => simp [rootScan_cons,ih,rootInsert,add_comm,add_left_comm]

theorem wordCounts_sum [Fintype V] (w : Word V) : ∑ v, wordCounts L w v = w.length := by
  rw [wordCounts,rootCounts_sum,rootScan_card]
  simp

theorem traceCounts_sum [Fintype V] (t : Trace L) :
    ∑ v, traceCounts L t v = traceLength L t := by
  induction t using Quotient.inductionOn with
  | h w => exact wordCounts_sum L w

theorem traceCounts_append_singleton (t : Trace L) (x : Letter V) :
    ∃ r, traceCounts L (appendTrace L t (ofWord L [x])) = traceCounts L t + Finsupp.single r 1 := by
  induction t using Quotient.inductionOn with
  | h w => exact ⟨_,wordCounts_append_singleton L w x⟩

omit [LinearOrder V] in
 theorem support_subset_singleton_add (c : V →₀ ℕ) (r : V) :
    c.support ⊆ (c + Finsupp.single r 1).support := by
  intro v hv
  apply Finsupp.mem_support_iff.mpr
  intro h
  apply Finsupp.mem_support_iff.mp hv
  exact (Nat.add_eq_zero_iff.mp (show c v + (Finsupp.single r 1) v = 0 from h)).1

theorem traceCounts_append_support (t : Trace L) (x : Letter V) :
    (traceCounts L t).support ⊆ (traceCounts L (appendTrace L t (ofWord L [x]))).support := by
  obtain ⟨r,hr⟩ := traceCounts_append_singleton L t x
  rw [hr]
  exact support_subset_singleton_add _ _

end RootCounts

variable (L)

/-- The normal trace of an element, obtained from the actual Artin presentation. -/
def groupNormalTrace : WordGroup L → Trace L :=
  Quotient.lift (fun w : FreeMonoid (Letter V) => normalTrace L (ofWord L w.toList))
    (fun _ _ h => h)

def artinNormalTrace (g : ArtinGroup L) : Trace L := groupNormalTrace L (ofArtin L g)

@[simp] theorem artinNormalTrace_word (w : Word V) :
    artinNormalTrace L (wordEval (artinGenerator L) w) = normalTrace L (ofWord L w) := by
  simp only [artinNormalTrace,ofArtin_word]
  rfl

theorem artinNormalTrace_reduced (g : ArtinGroup L) : Reduced L (artinNormalTrace L g) := by
  suffices ∀ h : WordGroup L, Reduced L (groupNormalTrace L h) from this _
  intro h
  induction h using Con.induction_on with
  | H w => exact normalTrace_reduced L (ofWord L w.toList)

theorem artinNormalTrace_eval (g : ArtinGroup L) :
    traceEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)
      (artinNormalTrace L g) = g := by
  suffices ∀ h : WordGroup L,
      traceEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)
        (groupNormalTrace L h) = toArtin L h by
    simpa only [artinNormalTrace,toArtin_ofArtin] using this (ofArtin L g)
  intro h
  induction h using Con.induction_on with
  | H w =>
      change traceEval L (artinGenerator L) _ (normalTrace L (ofWord L w.toList)) =
        toArtin L (groupWord L w.toList)
      rw [traceEval_normalTrace,traceEval_ofWord,toArtin_word]

theorem exists_reduced_word (g : ArtinGroup L) :
    ∃ w : Word V, Reduced L (ofWord L w) ∧ wordEval (artinGenerator L) w = g := by
  obtain ⟨w,hw⟩ := Quotient.exists_rep (artinNormalTrace L g)
  refine ⟨w,?_,?_⟩
  · rw [show ofWord L w = artinNormalTrace L g from hw]
    exact artinNormalTrace_reduced L g
  · change traceEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)
      (ofWord L w) = g
    rw [show ofWord L w = artinNormalTrace L g from hw]
    exact artinNormalTrace_eval L g

/-- A right generator step in the actual presented group is addition/removal
of exactly one maximal occurrence in its reduced trace. -/
theorem artinNormalTrace_right_step (g : ArtinGroup L) (x : Letter V) :
    (artinNormalTrace L (g * letterValue (artinGenerator L) x) =
      appendTrace L (artinNormalTrace L g) (ofWord L [x])) ∨
    (artinNormalTrace L g = appendTrace L
      (artinNormalTrace L (g * letterValue (artinGenerator L) x)) (ofWord L [invLetter x])) := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  have he : wordEval (artinGenerator L) w * letterValue (artinGenerator L) x =
      wordEval (artinGenerator L) (w ++ [x]) := by simp
  rw [he,artinNormalTrace_word,artinNormalTrace_word,hw.normalTrace_eq]
  rcases reduced_append_alternative hw with hl | ⟨v,hv,he,hn⟩
  · left
    exact hl.normalTrace_eq
  · right
    rw [hn]
    exact (ofWord_eq L).mpr he


section DirectionVectors
variable [Fintype V] [LinearOrder V]

/-- Barycentric direction, with value zero at the empty trace. -/
def traceDirection (t : Trace L) (v : V) : ℝ :=
  (traceCounts L t v : ℝ) / (traceLength L t : ℝ)

def artinDirection (g : ArtinGroup L) : V → ℝ :=
  traceDirection L (artinNormalTrace L g)

omit [Fintype V] in
theorem traceDirection_nonneg (t : Trace L) (v : V) : 0 ≤ traceDirection L t v :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem traceDirection_sum {t : Trace L} (ht : 0 < traceLength L t) :
    ∑ v, traceDirection L t v = 1 := by
  simp only [traceDirection,← Finset.sum_div,← Nat.cast_sum,traceCounts_sum]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht))

omit [Fintype V] [LinearOrder V] in
theorem traceLength_append_singleton (t : Trace L) (x : Letter V) :
    traceLength L (appendTrace L t (ofWord L [x])) = traceLength L t + 1 := by
  induction t using Quotient.inductionOn with
  | h w =>
      change (w ++ [x]).length = w.length + 1
      simp

/-- The exact finite-coordinate estimate used in the manuscript's direction map. -/
theorem count_normalization_bound (c : V →₀ ℕ) (r : V) {n : ℕ}
    (hn : 0 < n) (hs : ∑ v, c v = n) :
    ∑ v, |((c + Finsupp.single r 1 : V →₀ ℕ) v : ℝ) / (n + 1 : ℝ) -
      (c v : ℝ) / (n : ℝ)| ≤ 2 / (n + 1 : ℝ) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have hi (v : V) :
      ((c + Finsupp.single r 1 : V →₀ ℕ) v : ℝ) / (n + 1 : ℝ) - (c v : ℝ) / (n : ℝ) =
      (((Finsupp.single r (1 : ℕ)) v : ℝ) - (c v : ℝ) / n) / (n + 1 : ℝ) := by
    simp only [Finsupp.add_apply,Nat.cast_add]
    field_simp [hn0,ne_of_gt hd]
    ring
  have hpoint (v : V) :
      |((c + Finsupp.single r 1 : V →₀ ℕ) v : ℝ) / (n + 1 : ℝ) - (c v : ℝ) / (n : ℝ)| ≤
      (((Finsupp.single r (1 : ℕ)) v : ℝ) + (c v : ℝ) / n) / (n + 1 : ℝ) := by
    rw [hi,abs_div,abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ |(((Finsupp.single r (1 : ℕ)) v : ℝ))| + |(c v : ℝ) / n| :=
        abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  calc
    _ ≤ ∑ v, (((Finsupp.single r (1 : ℕ)) v : ℝ) + (c v : ℝ) / n) /
        (n + 1 : ℝ) := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = 2 / (n + 1 : ℝ) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.sum_div]
      simp only [← Nat.cast_sum,hs]
      norm_num [Finsupp.single_apply,div_self hn0]

theorem traceDirection_append_bound (t : Trace L) (x : Letter V)
    (ht : 0 < traceLength L t) :
    ∑ v, |traceDirection L (appendTrace L t (ofWord L [x])) v - traceDirection L t v| ≤
      2 / (traceLength L t + 1 : ℝ) := by
  obtain ⟨r,hr⟩ := traceCounts_append_singleton L t x
  simp only [traceDirection,traceLength_append_singleton,hr,Nat.cast_add,Nat.cast_one]
  exact count_normalization_bound (traceCounts L t) r ht (traceCounts_sum L t)

omit [Fintype V] in
theorem traceCounts_step_common_simplex (t : Trace L) (x : Letter V) :
    (((traceCounts L t).support ∪
      (traceCounts L (appendTrace L t (ofWord L [x]))).support : Finset V) : Set V).Pairwise L.Adj := by
  rw [Finset.union_eq_right.mpr (traceCounts_append_support L t x)]
  exact traceCounts_support_clique L _

/-- Full trace-direction step, for the actual generators of the Artin presentation.
The shorter normal trace controls both the common simplex and the uniform l1 bound. -/
theorem artinDirection_right_step (g : ArtinGroup L) (x : Letter V)
    (hg : 0 < traceLength L (artinNormalTrace L g))
    (hgx : 0 < traceLength L (artinNormalTrace L
      (g * letterValue (artinGenerator L) x))) :
    let t := artinNormalTrace L g
    let t' := artinNormalTrace L (g * letterValue (artinGenerator L) x)
    (((traceCounts L t).support ∪ (traceCounts L t').support : Finset V) : Set V).Pairwise L.Adj ∧
    ∃ n : ℕ, 0 < n ∧
      ((traceLength L t = n ∧ traceLength L t' = n + 1) ∨
        (traceLength L t' = n ∧ traceLength L t = n + 1)) ∧
      ∑ v, |artinDirection L (g * letterValue (artinGenerator L) x) v -
        artinDirection L g v| ≤ 2 / (n + 1 : ℝ) := by
  dsimp only
  rcases artinNormalTrace_right_step L g x with h | h
  · rw [h] at hgx ⊢
    refine ⟨traceCounts_step_common_simplex L _ x,
      traceLength L (artinNormalTrace L g),hg,Or.inl ⟨rfl,?_⟩,?_⟩
    · exact traceLength_append_singleton L _ x
    · simpa only [artinDirection,h] using
        traceDirection_append_bound L (artinNormalTrace L g) x hg
  · rw [h] at hg ⊢
    refine ⟨?_,traceLength L (artinNormalTrace L
      (g * letterValue (artinGenerator L) x)),hgx,Or.inr ⟨rfl,?_⟩,?_⟩
    · rw [Finset.union_comm]
      exact traceCounts_step_common_simplex L _ _
    · exact traceLength_append_singleton L _ _
    · simpa only [artinDirection,h,abs_sub_comm] using
        traceDirection_append_bound L
          (artinNormalTrace L (g * letterValue (artinGenerator L) x)) (invLetter x) hgx

end DirectionVectors


section CommutingPowerDirections
variable {L}

theorem Extract.mem {x : Letter V} {w v : Word V} (h : Extract L x w v) : x ∈ w := by
  induction h with
  | head => simp
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

theorem same_sign_reduced {w : Word V} (b : Bool) (hw : ∀ x ∈ w, x.2 = b) :
    Reduced L (ofWord L w) := by
  intro t ht
  obtain ⟨v,hv,_⟩ := ht.representative
  suffices ∀ {w v : Word V}, Step L w v → (∀ x ∈ w, x.2 = b) → False from this hv hw
  intro w v h
  induction h with
  | @head x w v he =>
      intro hh
      have hx := hh x (by simp)
      have hi := hh (invLetter x) (List.mem_cons_of_mem _ he.mem)
      simp only [invLetter,hx] at hi
      cases b <;> cases hi
  | cons x h ih =>
      intro hh
      exact ih (fun _ h => hh _ (List.mem_cons_of_mem _ h))

variable (L)
variable [LinearOrder V]

theorem nextRoot_self {s : Multiset (V × V)} {v : V}
    (hs : ∀ p ∈ s, p.2 = p.1) (hv : ∀ p ∈ s, p.1 = v ∨ L.Adj p.1 v) :
    nextRoot L s v = v := by
  classical
  unfold nextRoot
  split_ifs with h
  · obtain ⟨p,hp,hdep,hroot⟩ := mem_predecessorRoots.mp (Finset.min'_mem _ h)
    rw [← hroot,hs p hp]
    exact (hv p hp).resolve_right hdep
  · rfl

theorem rootScan_clique {C : Set V} (hC : C.Pairwise L.Adj)
    {s : Multiset (V × V)} (hs : ∀ p ∈ s, p.1 ∈ C ∧ p.2 = p.1)
    {w : Word V} (hw : ∀ x ∈ w, x.1 ∈ C) :
    rootScan L s w = ((w.map (fun x => (x.1,x.1))) : Multiset (V × V)) + s := by
  classical
  induction w generalizing s with
  | nil => simp
  | cons x w ih =>
      have hx : x.1 ∈ C := hw x (by simp)
      have hr : nextRoot L s x.1 = x.1 := by
        apply nextRoot_self L (fun p hp => (hs p hp).2)
        intro p hp
        by_cases hpv : p.1 = x.1
        · exact Or.inl hpv
        · exact Or.inr (hC (hs p hp).1 hx hpv)
      have hi : ∀ p ∈ rootInsert L s x.1, p.1 ∈ C ∧ p.2 = p.1 := by
        intro p hp
        simp only [rootInsert,hr,Multiset.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hx,rfl⟩
        · exact hs p hp
      rw [rootScan_cons,ih hi (fun y hy => hw y (List.mem_cons_of_mem _ hy))]
      simp [rootInsert,hr,← Multiset.cons_coe,Multiset.add_cons]

theorem wordCounts_clique {C : Set V} (hC : C.Pairwise L.Adj)
    {w : Word V} (hw : ∀ x ∈ w, x.1 ∈ C) :
    wordCounts L w = (w.map (fun x => Finsupp.single x.1 (1 : ℕ))).sum := by
  rw [wordCounts,rootScan_clique L hC (by simp) hw]
  simp only [add_zero,rootCounts,Multiset.map_coe,List.map_map,Multiset.sum_coe,Function.comp_def]

theorem counts_negative_commuting_powers {q r : V} (hqr : L.Adj q r) (n m : ℕ) :
    traceCounts L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m)) =
      Finsupp.single q n + Finsupp.single r m := by
  classical
  let w : Word V := List.replicate n (q,false) ++ List.replicate m (r,false)
  have hn : ∀ x ∈ w, x.2 = false := by
    intro x hx
    simp only [w,List.mem_append,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl
  have hC : ({q,r} : Set V).Pairwise L.Adj := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hqr
    · exact L.symm.symm _ _ hqr
    · exact False.elim (hab rfl)
  have hwc : ∀ x ∈ w, x.1 ∈ ({q,r} : Set V) := by
    intro x hx
    simp only [w,List.mem_append,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
  have he : wordEval (artinGenerator L) w =
      (artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m := by
    simp [wordEval,w,List.map_replicate]
  rw [← he,artinNormalTrace_word,(same_sign_reduced false hn).normalTrace_eq,
    traceCounts_ofWord,wordCounts_clique L hC hwc]
  ext v
  simp [w,List.map_replicate,Finsupp.single_apply]

end CommutingPowerDirections

section HeightAndExactDirections

@[simp] theorem height_generator (v : V) :
    height L (artinGenerator L v) = Multiplicative.ofAdd 1 := PresentedGroup.toGroup.of _

def wordHeight (w : Word V) : ℤ := (w.map fun x => if x.2 then 1 else -1).sum

@[simp] theorem wordHeight_nil : wordHeight ([] : Word V) = 0 := rfl
@[simp] theorem wordHeight_cons (x : Letter V) (w : Word V) :
    wordHeight (x :: w) = (if x.2 then 1 else -1) + wordHeight w := rfl

theorem height_wordEval (w : Word V) :
    (height L (wordEval (artinGenerator L) w)).toAdd = wordHeight w := by
  induction w with
  | nil => simp [wordEval]
  | cons x w ih =>
      simp only [wordEval,List.map_cons,List.prod_cons,map_mul,
        wordHeight_cons] at *
      change (height L (letterValue (artinGenerator L) x)).toAdd +
        (height L ((w.map (letterValue (artinGenerator L))).prod)).toAdd = _
      rw [ih]
      congr 1
      cases x with
      | mk v b => cases b <;> simp [letterValue]

theorem wordHeight_abs_le (w : Word V) : |wordHeight w| ≤ (w.length : ℤ) := by
  induction w with
  | nil => simp
  | cons x w ih =>
      rw [wordHeight_cons]
      calc
        _ ≤ |(if x.2 then 1 else -1 : ℤ)| + |wordHeight w| := abs_add_le _ _
        _ = 1 + |wordHeight w| := by cases x.2 <;> norm_num
        _ ≤ ((x :: w).length : ℤ) := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega

theorem height_abs_le_traceLength (g : ArtinGroup L) :
    |(height L g).toAdd| ≤ (traceLength L (artinNormalTrace L g) : ℤ) := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  rw [height_wordEval,artinNormalTrace_word,hw.normalTrace_eq]
  exact wordHeight_abs_le w

theorem traceLength_pos_of_height_ne {g : ArtinGroup L} (h : (height L g).toAdd ≠ 0) :
    0 < traceLength L (artinNormalTrace L g) := by
  have hh := height_abs_le_traceLength L g
  have ha := abs_pos.mpr h
  omega

variable [Fintype V] [LinearOrder V]

theorem length_negative_commuting_powers {q r : V} (hqr : L.Adj q r) (n m : ℕ) :
    traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m)) = n + m := by
  rw [← traceCounts_sum,counts_negative_commuting_powers L hqr]
  simp [Finsupp.single_apply,Finset.sum_add_distrib]

theorem direction_negative_commuting_powers {q r : V} (hqr : L.Adj q r)
    (n m : ℕ) (v : V) :
    artinDirection L ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m) v =
      ((if q = v then n else 0 : ℕ) + (if r = v then m else 0 : ℕ) : ℝ) / (n + m : ℝ) := by
  rw [artinDirection,traceDirection,counts_negative_commuting_powers L hqr,
    length_negative_commuting_powers L hqr]
  simp only [Finsupp.add_apply,Finsupp.single_apply,Nat.cast_add,Nat.cast_ite,Nat.cast_zero]

end HeightAndExactDirections

end TraceWords

end EilenbergGanea

end

end OAI
