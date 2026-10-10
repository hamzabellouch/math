import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperInterpreter

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

def retape (s : State Q K g) (i : BitTape) : State Q K g := {s with input:=i}

def SlowLink (P : Processor Q K g) (s z : State Q K g) : Prop :=
  z.yielded=true ∧ z.outputRev=[] ∧ ∀w coin,step P (install s w) coin=retape z (BitTape.ofWord w)

structure Prefix (P : Processor Q K g) (a z : State Q K g) (d : ℕ) where
  state : ℕ→State Q K g
  start : state 0=a
  finish : state d=z
  next : ∀j<d,SlowLink P (state j) (state (j+1))

 def Prefix.append {P : Processor Q K g} {a b c : State Q K g} {d e : ℕ}
    (h : Prefix P a b d) (h' : Prefix P b c e) : Prefix P a c (d+e) := by
  let f:=fun j=>if j<d then h.state j else h'.state (j-d)
  refine ⟨f,?_,?_,?_⟩
  · dsimp [f]
    split_ifs with hd
    · exact h.start
    · have he : d=0:=by omega
      subst d
      simpa only [Nat.sub_self,h'.start] using h.finish.symm.trans h.start
  · simpa only [f,show ¬d+e<d by omega,↓reduceIte,Nat.add_sub_cancel_left] using h'.finish
  · intro j hj
    dsimp [f]
    by_cases hd : j<d
    · rw [ite_eq_left hd]
      by_cases hs : j+1<d
      · rw [ite_eq_left hs];exact h.next j hd
      · rw [ite_eq_right hs]
        have he : j+1=d:=by omega
        rw [he,Nat.sub_self,h'.start]
        have hh:=h.next j hd
        rw [he,h.finish] at hh
        exact hh
    · rw [ite_eq_right hd,ite_eq_right (by omega)]
      have he : j+1-d=(j-d)+1:=by omega
      rw [he]
      exact h'.next (j-d) (by omega)

 theorem SlowLink.run {P : Processor Q K g} {a b : State Q K g} (h : SlowLink P a b)
    (w bs : List Bool) (hb : 1≤bs.length) :
    run P (install a w) bs=retape b (BitTape.ofWord w) := by
  cases bs with
  | nil=>simp at hb
  | cons c bs=>
    rw [run_cons,h.2.2]
    exact run_yielded P (retape b (BitTape.ofWord w)) h.1 bs

 theorem install_retape (s : State Q K g) (i : BitTape) (w : List Bool) :
    install (retape s i) w=install s w := rfl

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 def constructor_prefix (hC : StackPrimitive.Deterministic C)
    (s : StackCompiler.State qc (Fintype.card K') g) (t : ℕ)
    (ht : ∀j<t,(StackCompiler.run C s (List.replicate j false)).yielded=false) :
    Prefix (processor C A) (constructState s BitTape.blank)
      (constructState (StackCompiler.run C s (List.replicate t false)) BitTape.blank) t := by
  refine ⟨fun j=>constructState (StackCompiler.run C s (List.replicate j false)) BitTape.blank,rfl,rfl,?_⟩
  intro j hj
  refine ⟨rfl,rfl,?_⟩
  intro w coin
  rw [cap_succ]
  exact construct_step C A hC _ (ht j hj) (BitTape.ofWord w) coin

 theorem pad_digit (i : BitTape) (a : Bool) (m : List (Fin g)) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .pad i (digit a::m) [] []) coin=
      wordState .pad i m [] [] [] true := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_ne_sep,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem pad_sep (i : BitTape) (m : List (Fin g)) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .pad i (sep::m) [] []) coin=
      wordState .sample i m [] [] [] true := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 def padding_prefix (w : List Bool) (m : List (Fin g)) :
    Prefix (processor C A) (wordState .pad BitTape.blank (w.map digit++sep::m) [] [] [] true)
      (wordState .sample BitTape.blank m [] [] [] true) (w.length+1) := by
  induction w with
  | nil=>
    refine ⟨fun j=>if j=0 then wordState .pad BitTape.blank (sep::m) [] [] [] true
      else wordState .sample BitTape.blank m [] [] [] true,by simp,by simp,?_⟩
    intro j hj
    have he : j=0:=by simp only [List.length_nil] at hj;omega
    subst j
    simp only [↓reduceIte,Nat.zero_add,Nat.one_ne_zero]
    exact ⟨rfl,rfl,fun a b=>pad_sep C A (BitTape.ofWord a) m b⟩
  | cons b w ih=>
    have h : Prefix (processor C A)
        (wordState .pad BitTape.blank ((b::w).map digit++sep::m) [] [] [] true)
        (wordState .pad BitTape.blank (w.map digit++sep::m) [] [] [] true) 1 := by
      refine ⟨fun j=>if j=0 then wordState .pad BitTape.blank ((b::w).map digit++sep::m) [] [] [] true
        else wordState .pad BitTape.blank (w.map digit++sep::m) [] [] [] true,by simp,by simp,?_⟩
      intro j hj
      have he : j=0:=by omega
      subst j
      simp only [↓reduceIte,Nat.zero_add,Nat.one_ne_zero]
      exact ⟨rfl,rfl,fun a c=>pad_digit C A (BitTape.ofWord a) b (w.map digit++sep::m) c⟩
    convert h.append ih using 1
    simp [List.length_cons,Nat.add_comm]

end UniformKServer.UniformWrapper

end

end OAI
