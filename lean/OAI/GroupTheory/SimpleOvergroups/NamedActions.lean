import Mathlib
import OAI.GroupTheory.SimpleOvergroups.BoundedContexts

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction

structure Operations (G X : Type*) where
  one : G
  mul : G → G → G
  inv : G → G
  act : G → X → X
  gcost : G → ℕ
  xcost : X → ℕ
  cost_one : gcost one = 0
  cost_mul : ∀ g h, gcost (mul g h) = gcost g + gcost h
  cost_inv : ∀ g, gcost (inv g) = gcost g
  cost_act : ∀ g x, xcost (act g x) = gcost g + xcost x

abbrev Letter (G X : Type*) := G ⊕ (X ⊕ Option X)
abbrev Form (G X : Type*) := Option (List X × G × List X)
abbrev Result (K L : Type*) := Option (List L × K × List L)

namespace Operations
variable {G X K L : Type*} (N : Operations G X)

def letterCost : Letter G X → ℕ
  | .inl g => N.gcost g
  | .inr (.inl x) | .inr (.inr (some x)) => N.xcost x
  | .inr (.inr none) => 0

def wordCost (w : List (Letter G X)) : ℕ := (w.map N.letterCost).sum

def formCost : Form G X → ℕ
  | none => 0
  | some (l,g,r) => (l.map N.xcost).sum + N.gcost g + (r.map N.xcost).sum

def formKey (kg : G → K) (kx : X → L) : Form G X → Result K L :=
  Option.map (fun p => (p.1.map kx,kg p.2.1,p.2.2.map kx))

def plan : Letter G X → Form G X → Form G X ⊕ (X × X × Form G X)
  | _, none => .inl none
  | .inr (.inr none), _ => .inl none
  | .inr (.inl x), some (l,g,r) => .inl (some (x::l,g,r))
  | .inl h, some ([],g,r) => .inl (some ([],N.mul h g,r))
  | .inl h, some (x::l,g,r) => .inl (some (N.act h x::l,g,r))
  | .inr (.inr (some y)), some ([],g,r) =>
      .inl (some ([],N.one,r++[N.act (N.inv g) y]))
  | .inr (.inr (some y)), some (x::l,g,r) => .inr (y,x,some (l,g,r))

variable [DecidableEq L]

def totalStep (kx : X → L) (a : Letter G X) (f : Form G X) : Form G X :=
  (N.plan a f).elim id (fun p => if kx p.1 = kx p.2.1 then p.2.2 else none)

def totalRun (kx : X → L) (w : List (Letter G X)) (f : Form G X) : Form G X :=
  w.foldr (N.totalStep kx) f

def totalNormalize (kx : X → L) (w : List (Letter G X)) : Form G X :=
  N.totalRun kx w (some ([],N.one,[]))

def totalTest (kg : G → K) (kx : X → L) (w : List (Letter G X)) : Result K L :=
  formKey kg kx (N.totalNormalize kx w)

@[simp] theorem totalRun_nil (kx : X → L) (f : Form G X) : N.totalRun kx [] f = f := rfl
@[simp] theorem totalRun_cons (kx : X → L) (a : Letter G X) (w : List (Letter G X))
    (f : Form G X) : N.totalRun kx (a::w) f = N.totalStep kx a (N.totalRun kx w f) := rfl
@[simp] theorem wordCost_nil : N.wordCost [] = 0 := rfl
@[simp] theorem wordCost_cons (a : Letter G X) (w : List (Letter G X)) :
    N.wordCost (a::w) = N.letterCost a + N.wordCost w := rfl
@[simp] theorem wordCost_append (u v : List (Letter G X)) :
    N.wordCost (u++v) = N.wordCost u + N.wordCost v := by simp [wordCost]
@[simp] theorem totalStep_none (kx : X → L) (a : Letter G X) :
    N.totalStep kx a none = none := rfl

theorem totalStep_cost (kx : X → L) (a : Letter G X) (f : Form G X) :
    N.formCost (N.totalStep kx a f) ≤ N.letterCost a + N.formCost f := by
  cases f with
  | none => simp [formCost]
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> simp [totalStep,plan,formCost,letterCost,N.cost_mul,N.cost_act] <;> omega
    · simp [totalStep,plan,formCost,letterCost]; omega
    · cases y with
      | none => simp [totalStep,plan,formCost,letterCost]
      | some y =>
        cases l with
        | nil => simp [totalStep,plan,formCost,letterCost,N.cost_one,N.cost_act,N.cost_inv]; omega
        | cons x l =>
          by_cases h : kx y = kx x <;> simp [totalStep,plan,h,formCost,letterCost]; omega

theorem totalRun_cost (kx : X → L) (w : List (Letter G X)) (f : Form G X) :
    N.formCost (N.totalRun kx w f) ≤ N.wordCost w + N.formCost f := by
  induction w with
  | nil => simp
  | cons a w ih =>
    exact (N.totalStep_cost kx a (N.totalRun kx w f)).trans (by rw [wordCost_cons]; omega)

theorem totalNormalize_cost (kx : X → L) (w : List (Letter G X)) :
    N.formCost (N.totalNormalize kx w) ≤ N.wordCost w := by
  simpa [totalNormalize,formCost,N.cost_one] using N.totalRun_cost kx w (some ([],N.one,[]))

end Operations

structure Interpretation {G X V Y K L : Type*} [Group V] [MulAction V Y]
    {m : ℕ} (N : Operations G X) (C : ActionCalculus V Y K L m) where
  group : G → C.GLabel
  point : X → C.XLabel
  group_cost : ∀ g, (group g).cost = N.gcost g
  point_cost : ∀ x, (point x).cost = N.xcost x
  one : group N.one = C.identity
  mul : ∀ g h, group (N.mul g h) = C.multiply (group g) (group h)
  inv : ∀ g, group (N.inv g) = C.inverse (group g)
  act : ∀ g x, point (N.act g x) = C.act (group g) (point x)

namespace Interpretation
variable {G X V Y K L : Type*} [Group V] [MulAction V Y] {m : ℕ}
  {N : Operations G X} {C : ActionCalculus V Y K L m} (I : Interpretation N C)

def gkey (g : G) : K := (I.group g).key
def xkey (x : X) : L := (I.point x).key

def letter : Letter G X → C.Letter
  | .inl g => .grp (I.group g)
  | .inr (.inl x) => .pre (I.point x)
  | .inr (.inr (some x)) => .del (I.point x)
  | .inr (.inr none) => .zero

def form : Form G X → C.Form :=
  Option.map (fun p => (p.1.map I.point,I.group p.2.1,p.2.2.map I.point))

@[simp] theorem letter_cost (a : Letter G X) : (I.letter a).cost C = N.letterCost a := by
  rcases a with g | (x | y)
  · exact I.group_cost g
  · exact I.point_cost x
  · cases y with
    | none => rfl
    | some x => exact I.point_cost x

@[simp] theorem form_cost (f : Form G X) : (I.form f).cost C = N.formCost f := by
  cases f with
  | none => rfl
  | some p => simp [form,ActionCalculus.Form.cost,Operations.formCost,List.map_map,
      Function.comp_def,I.point_cost,I.group_cost]

@[simp] theorem word_cost (w : List (Letter G X)) : C.wordCost (w.map I.letter) = N.wordCost w := by
  simp [ActionCalculus.wordCost,Operations.wordCost,List.map_map,Function.comp_def]

@[simp] theorem form_key (f : Form G X) :
    (I.form f).key C = Operations.formKey I.gkey I.xkey f := by
  cases f <;> simp [form,Operations.formKey,ActionCalculus.Form.key,List.map_map,
    Function.comp_def,gkey,xkey]

variable [DecidableEq L]

theorem totalStep (a : Letter G X) (f : Form G X) :
    I.form (N.totalStep I.xkey a f) = C.step (I.letter a) (I.form f) := by
  cases f with
  | none => simp [form]
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,I.mul,I.act]
    · simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step]
    · cases y with
      | none => rfl
      | some y =>
        cases l with
        | nil => simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,I.one,I.inv,I.act]
        | cons x l =>
          by_cases h : I.xkey y = I.xkey x
          · change (I.point y).key = (I.point x).key at h
            simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,xkey,h]
          · change (I.point y).key ≠ (I.point x).key at h
            simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,xkey,h]

theorem totalRun (w : List (Letter G X)) (f : Form G X) :
    I.form (N.totalRun I.xkey w f) = C.run (w.map I.letter) (I.form f) := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [Operations.totalRun_cons,I.totalStep,ih,List.map_cons,ActionCalculus.run_cons]

theorem totalNormalize (w : List (Letter G X)) :
    I.form (N.totalNormalize I.xkey w) = C.normalize (w.map I.letter) := by
  unfold Operations.totalNormalize
  rw [I.totalRun]
  simp only [form,Option.map_some,List.map_nil,I.one]
  rfl

theorem totalTest (w : List (Letter G X)) :
    N.totalTest I.gkey I.xkey w = (C.normalize (w.map I.letter)).key C := by
  rw [← I.totalNormalize,I.form_key]
  rfl

theorem totalTest_context {u v a b : List (Letter G X)} {d : ℕ}
    (h : N.totalTest I.gkey I.xkey u = N.totalTest I.gkey I.xkey v)
    (hu : N.wordCost (a++u++b) ≤ d) (hv : N.wordCost (a++v++b) ≤ d) (hm : 3*d ≤ m) :
    N.totalTest I.gkey I.xkey (a++u++b) = N.totalTest I.gkey I.xkey (a++v++b) := by
  simp only [I.totalTest,List.map_append] at h ⊢
  apply C.normalize_context h (hm := hm)
  · simpa only [← List.map_append,I.word_cost] using hu
  · simpa only [← List.map_append,I.word_cost] using hv

theorem totalTest_zero_context {u a b : List (Letter G X)} {d : ℕ}
    (h : N.totalTest I.gkey I.xkey u = none)
    (hu : N.wordCost (a++u++b) ≤ d) (hm : 3*d ≤ m) :
    N.totalTest I.gkey I.xkey (a++u++b) = none := by
  simp only [I.totalTest,List.map_append] at h ⊢
  exact C.normalize_zero_context h (by simpa only [← List.map_append,I.word_cost] using hu) hm

@[simp] theorem totalTest_nil : N.totalTest I.gkey I.xkey [] ≠ none := by
  simp only [I.totalTest,List.map_nil]
  exact C.normalize_nil_ne_zero

end Interpretation
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction

end OAI
