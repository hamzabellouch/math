import OAI.Computability.MatchingCount.RecursiveBounds

namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode
variable {A B C P : Type}

def paramStep (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : P×State A B C) : P×State A B C :=
  (z.1,step (zero z.1) (expand z.1) (combine z.1) z.2)

lemma paramStep_iterate (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : P×State A B C) (k : ℕ) :
    (paramStep zero expand combine)^[k] z=
      (z.1,(step (zero z.1) (expand z.1) (combine z.1))^[k] z.2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',ih,paramStep]

namespace Compile
open StackCode.Poly
variable [Coding A] [Coding B] [Coding C] [Coding P]
  [Inhabited A] [Inhabited B] [Inhabited C]

def execCommand (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : (P×State A B C)×Command A C) : State A B C :=
  match z.2 with
  | .call k a => if k=0 then (z.1.2.1.tail,zero z.1.1::z.1.2.2) else
    match expand z.1.1 a with
    | .leaf b => (z.1.2.1.tail,b::z.1.2.2)
    | .fork c x y => (.call (k-1) x::.call (k-1) y::.join c::z.1.2.1.tail,z.1.2.2)
  | .join c => if 2≤z.1.2.2.length then
      (z.1.2.1.tail,combine z.1.1 c (z.1.2.2.tail.headD default) (z.1.2.2.headD default)::z.1.2.2.tail.tail)
    else ([],z.1.2.2)

@[fun_prop] theorem execCommand_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (execCommand zero expand combine) := by
  unfold execCommand
  apply commandCasesWith Prod.snd
    (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
      if z.2.1=0 then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
      match expand z.1.1.1 z.2.2 with
      | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
      | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2))
    (fun z => if 2≤z.1.1.2.2.length then
      (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
      else ([],z.1.1.2.2))
  · fun_prop
  · have hb₀ := branchCasesWith
      (fun z : ((P×State A B C)×Command A C)×(ℕ×A) => expand z.1.1.1 z.2.2)
      (fun z => (z.1.1.1.2.1.tail,z.2::z.1.1.1.2.2))
      (fun z => (Command.call (z.1.2.1-1) z.2.2.1::Command.call (z.1.2.1-1) z.2.2.2::
        Command.join z.2.1::z.1.1.1.2.1.tail,z.1.1.1.2.2))
      (by fun_prop) (by fun_prop) (by fun_prop)
    have hb : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) :=
      hb₀.congr (fun z => by cases expand z.1.1.1 z.2.2 <;> rfl)
    have h : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        if decide (z.2.1=0) then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)
  · have h : Poly (fun z : ((P×State A B C)×Command A C)×C => if decide (2≤z.1.1.2.2.length) then
        (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
        else ([],z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)

@[fun_prop] theorem paramStep_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (paramStep zero expand combine) := by
  have hx := execCommand_poly zero expand combine hz he hc
  have h : Poly (fun z : P×State A B C =>
      (z.1,if z.2.1.isEmpty then z.2 else execCommand zero expand combine (z,z.2.1.headD default))) := by fun_prop
  apply h.congr
  intro z
  rcases z with ⟨p,w,v⟩
  unfold paramStep
  cases w with
  | nil => rfl
  | cons a w =>
    cases a with
    | call k a =>
      cases k <;> rfl
    | join c =>
      cases v with
      | nil => simp [execCommand,step]
      | cons b v => cases v <;> simp [execCommand,step]
end Compile
end BinaryMatching.RecursiveEval
end

end OAI
