import Mathlib
import OAI.Combinatorics.UniformKServer.UniformWrapper

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

def UniformRun (P : Processor Q K g) (s : State Q K g) (t : ℕ) (z : State Q K g) : Prop :=
  ∀bs : List Bool,bs.length=t → run P s bs=z

theorem uniform_zero (P : Processor Q K g) (s : State Q K g) : UniformRun P s 0 s := by
  intro bs h;have hh:=List.eq_nil_of_length_eq_zero h;subst bs;rfl

theorem uniform_step (P : Processor Q K g) (s z : State Q K g) (h : ∀b,step P s b=z) :
    UniformRun P s 1 z := by
  intro bs hb
  cases bs with
  | nil=>simp at hb
  | cons b bs=>
    have he : bs=[]:=List.eq_nil_of_length_eq_zero (by simpa using hb)
    subst bs
    exact h b

theorem UniformRun.trans {P : Processor Q K g} {s z w : State Q K g} {t u : ℕ}
    (h : UniformRun P s t z) (h' : UniformRun P z u w) : UniformRun P s (t+u) w := by
  intro bs hb
  rw [←List.take_append_drop t bs,run_append,h (bs.take t) (by simp only [List.length_take,hb];omega)]
  exact h' _ (by simp only [List.length_drop,hb];omega)

theorem UniformRun.mono {P : Processor Q K g} {s z : State Q K g} {t u : ℕ}
    (h : UniformRun P s t z) (hy : z.yielded=true) (hu : t≤u) : UniformRun P s u z := by
  intro bs hb
  rw [←List.take_append_drop t bs,run_append,h (bs.take t) (by simp only [List.length_take,hb];omega)]
  exact run_yielded P z hy _

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}

def wordState (q : Control qc qa) (input : BitTape) (m p b : List (Fin g))
    (out : List Bool:=[]) (y : Bool:=false) : State qc qa :=
  ⟨q,input,(fun i=>match i with
    | .base .main=>m | .pay=>p | .buf=>b | _=>[]),out,y⟩

@[simp] theorem digit_ne_sep (b : Bool) : digit b≠sep := by
  intro h
  have he:=FlatTM2.letters.injective h
  cases b <;> cases he
@[simp] theorem sep_ne_digit (b : Bool) : sep≠digit b := Ne.symm (digit_ne_sep b)
@[simp] theorem digit_eq_digit (b c : Bool) : digit b=digit c ↔ b=c := by
  constructor
  · intro h;have he:=FlatTM2.letters.injective h;cases b <;> cases c <;> cases he <;> rfl
  · rintro rfl;rfl

theorem wordState_ext {s z : State qc qa} (hc : s.control=z.control) (hi : s.input=z.input)
    (hs : ∀k,s.store k=z.store k) (ho : s.outputRev=z.outputRev) (hy : s.yielded=z.yielded) : s=z := by
  cases s;cases z;simp_all only
  congr
  exact funext hs

variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem step_bootCons (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .bootCons i [] [] []) coin=
      wordState .bootOne i [sep] [] [] := by
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem step_bootOne (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .bootOne i [sep] [] []) coin=
      wordState .bootRead i [digit true,sep] [] [] := by
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

end UniformKServer.UniformWrapper

end

end OAI
