import Mathlib
import OAI.GroupTheory.SimpleOvergroups.TruncatedAction

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding

structure WithBound {A K : Type*} (B : KeyBall A K) where
  val : A
  cost : ℕ
  mem : val ∈ B.ball cost

namespace WithBound
variable {A K : Type*} {B : KeyBall A K}
def key (a : WithBound B) : K := B.key a.val
end WithBound

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m)

abbrev GLabel := WithBound C.group
abbrev XLabel := WithBound C.point

def identity : C.GLabel := ⟨1,0,C.one_mem 0⟩
def multiply (g h : C.GLabel) : C.GLabel :=
  ⟨g.val*h.val, g.cost+h.cost, C.mul_mem g.mem h.mem⟩
def inverse (g : C.GLabel) : C.GLabel := ⟨g.val⁻¹,g.cost,C.inv_mem g.mem⟩
def act (g : C.GLabel) (x : C.XLabel) : C.XLabel :=
  ⟨g.val • x.val,g.cost+x.cost,C.smul_mem g.mem x.mem⟩

inductive Letter where
  | grp : C.GLabel → Letter
  | pre : C.XLabel → Letter
  | del : C.XLabel → Letter
  | zero : Letter

namespace Letter
def cost : C.Letter → ℕ
  | .grp g => g.cost
  | .pre x | .del x => x.cost
  | .zero => 0

def key : C.Letter → Sum K (Sum L (Option L))
  | .grp g => .inl g.key
  | .pre x => .inr (.inl x.key)
  | .del x => .inr (.inr (some x.key))
  | .zero => .inr (.inr none)
end Letter

abbrev Form := Option (List C.XLabel × C.GLabel × List C.XLabel)

namespace Form
def cost : C.Form → ℕ
  | none => 0
  | some (l,g,r) => (l.map WithBound.cost).sum + g.cost + (r.map WithBound.cost).sum

def key : C.Form → Option (List L × K × List L) :=
  Option.map (fun p => (p.1.map WithBound.key, p.2.1.key, p.2.2.map WithBound.key))
end Form

def wordCost (w : List C.Letter) : ℕ := (w.map (Letter.cost C)).sum

@[simp] theorem wordCost_nil : C.wordCost [] = 0 := rfl
@[simp] theorem wordCost_cons (a : C.Letter) (w : List C.Letter) :
    C.wordCost (a::w) = a.cost C + C.wordCost w := rfl
@[simp] theorem wordCost_append (a b : List C.Letter) :
    C.wordCost (a++b) = C.wordCost a + C.wordCost b := by simp [wordCost]

variable [DecidableEq L]

def step : C.Letter → C.Form → C.Form
  | _, none => none
  | .zero, _ => none
  | .pre x, some (l,g,r) => some (x::l,g,r)
  | .grp h, some ([],g,r) => some ([],C.multiply h g,r)
  | .grp h, some (x::l,g,r) => some (C.act h x::l,g,r)
  | .del y, some ([],g,r) => some ([],C.identity,r++[C.act (C.inverse g) y])
  | .del y, some (x::l,g,r) => if y.key = x.key then some (l,g,r) else none

def run (w : List C.Letter) (f : C.Form) : C.Form :=
  w.foldr (C.step) f

def normalize (w : List C.Letter) : C.Form := C.run w (some ([],C.identity,[]))

@[simp] theorem run_nil (f : C.Form) : C.run [] f = f := rfl
@[simp] theorem run_cons (a : C.Letter) (w : List C.Letter) (f : C.Form) :
    C.run (a::w) f = C.step a (C.run w f) := rfl
@[simp] theorem run_append (a b : List C.Letter) (f : C.Form) :
    C.run (a++b) f = C.run a (C.run b f) := by simp [run]

@[simp] theorem step_none (a : C.Letter) : C.step a none = none := by cases a <;> rfl
@[simp] theorem run_none (w : List C.Letter) : C.run w none = none := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

theorem step_cost (a : C.Letter) (f : C.Form) :
    (C.step a f).cost C ≤ a.cost C + f.cost C := by
  cases f with
  | none => simp [Form.cost]
  | some p =>
    rcases p with ⟨l,g,r⟩
    cases a with
    | zero => simp [step,Form.cost]
    | pre x => simp [step,Form.cost,Letter.cost]; omega
    | grp h =>
      cases l <;> simp [step,Form.cost,Letter.cost,multiply,act] <;> omega
    | del y =>
      cases l with
      | nil => simp [step,Form.cost,Letter.cost,act,inverse,identity]; omega
      | cons x l =>
        by_cases h : y.key = x.key <;> simp [step,h,Form.cost,Letter.cost]; omega

theorem run_cost (w : List C.Letter) (f : C.Form) :
    (C.run w f).cost C ≤ C.wordCost w + f.cost C := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [run_cons]
    exact (C.step_cost a (C.run w f)).trans (by simp only [wordCost_cons]; omega)

theorem normalize_cost (w : List C.Letter) :
    (C.normalize w).cost C ≤ C.wordCost w := by
  simpa [normalize, Form.cost, identity] using C.run_cost w (some ([],C.identity,[]))

theorem step_congr {a a' : C.Letter} {f f' : C.Form}
    (ha : a.key C = a'.key C) (hf : f.key C = f'.key C)
    (hb : a.cost C + f.cost C ≤ m) (hb' : a'.cost C + f'.cost C ≤ m) :
    (C.step a f).key C = (C.step a' f').key C := by
  cases f with
  | none =>
    cases f' with
    | none => simp
    | some p => simp [Form.key] at hf
  | some p =>
    cases f' with
    | none => simp [Form.key] at hf
    | some p' =>
      rcases p with ⟨l,g,r⟩
      rcases p' with ⟨l',g',r'⟩
      simp only [Form.key, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨hl,hg,hr⟩ := hf
      cases a <;> cases a' <;> simp only [Letter.key, Sum.inl.injEq, Sum.inr.injEq,
        Option.some.injEq, reduceCtorEq] at ha
      case pre.pre x x' => simp [step,Form.key,ha,hl,hg,hr]
      case zero.zero => rfl
      case grp.grp h h' =>
        cases l with
        | nil =>
          have he : l' = [] := by simpa using hl.symm
          subst l'
          have he := C.mul_congr h.mem g.mem h'.mem g'.mem
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb; omega)
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb'; omega) ha hg
          simp [step,Form.key,multiply,WithBound.key, he,hr]
        | cons x l =>
          cases l' with
          | nil => simp at hl
          | cons x' l' =>
            simp only [List.map_cons, List.cons.injEq] at hl
            have he := C.smul_congr h.mem x.mem h'.mem x'.mem
              (by simp only [Letter.cost,Form.cost,List.map_cons,List.sum_cons] at hb; omega)
              (by simp only [Letter.cost,Form.cost,List.map_cons,List.sum_cons] at hb'; omega)
              ha hl.1
            change (C.act h x).key = (C.act h' x').key at he
            simp only [step,Form.key,Option.map_some,List.map_cons,he,hl.2,hg,hr]
      case del.del y y' =>
        cases l with
        | nil =>
          have he : l' = [] := by simpa using hl.symm
          subst l'
          have he := C.smul_congr (C.inv_mem g.mem) y.mem (C.inv_mem g'.mem) y'.mem
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb; omega)
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb'; omega)
            (C.inv_congr hg) ha
          simp [step,Form.key,act,inverse,WithBound.key,he,hr]
        | cons x l =>
          cases l' with
          | nil => simp at hl
          | cons x' l' =>
            simp only [List.map_cons,List.cons.injEq] at hl
            simp only [step,ha,hl.1]
            split <;> simp [Form.key,hl.2,hg,hr]

theorem run_congr {w w' : List C.Letter} {f f' : C.Form}
    (hw : w.map (Letter.key C) = w'.map (Letter.key C))
    (hf : f.key C = f'.key C)
    (hb : C.wordCost w + f.cost C ≤ m) (hb' : C.wordCost w' + f'.cost C ≤ m) :
    (C.run w f).key C = (C.run w' f').key C := by
  induction w generalizing w' with
  | nil =>
    have he : w' = [] := by simpa using hw.symm
    subst w'
    exact hf
  | cons a w ih =>
    cases w' with
    | nil => simp at hw
    | cons a' w' =>
      simp only [List.map_cons,List.cons.injEq] at hw
      have ht : C.wordCost w + f.cost C ≤ m := by simp only [wordCost_cons] at hb; omega
      have ht' : C.wordCost w' + f'.cost C ≤ m := by simp only [wordCost_cons] at hb'; omega
      rw [run_cons,run_cons]
      exact C.step_congr hw.1 (ih hw.2 ht ht')
        (by have := C.run_cost w f; simp only [wordCost_cons] at hb; omega)
        (by have := C.run_cost w' f'; simp only [wordCost_cons] at hb'; omega)

theorem normalize_left_context {u v a : List C.Letter}
    (he : (C.normalize u).key C = (C.normalize v).key C)
    (hu : C.wordCost (a++u) ≤ m) (hv : C.wordCost (a++v) ≤ m) :
    (C.normalize (a++u)).key C = (C.normalize (a++v)).key C := by
  simp only [normalize,run_append]
  apply C.run_congr rfl he
  · have := C.normalize_cost u
    simp only [wordCost_append] at hu
    omega
  · have := C.normalize_cost v
    simp only [wordCost_append] at hv
    omega

end ActionCalculus
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
