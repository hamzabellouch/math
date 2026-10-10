import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperAlgebra

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

def tape (l : List (Option Bool)) : List Bool→BitTape
  | []=>⟨l,none,[]⟩
  | b::bs=>⟨l,some b,bs.map some⟩
@[simp] theorem ofWord_tape (w : List Bool) : BitTape.ofWord w=tape [] w := by cases w <;> rfl
@[simp] theorem tape_shift (l : List (Option Bool)) (b : Bool) (w : List Bool) :
    (tape l (b::w)).shift .right=tape (some b::l) w := by cases w <;> rfl

theorem read_step (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (b : Bool) (w : List Bool) (m p buf : List (Fin g))
    (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q (tape l (b::w)) m p buf out) coin=
      wordState q (tape (some b::l) w) m p (digit b::buf) out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,read,write]
  apply wordState_ext
  · rfl
  · exact tape_shift _ _ _
  · intro k;cases k with
    | base k=>cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

theorem read_empty (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (m p buf : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q (tape l []) m p buf out) coin=
      wordState exit (tape l []) m p buf out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,read,pass,tape,BitTape.shift]
  rfl

theorem read_run (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (w : List Bool) (m p buf : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q (tape l w) m p buf out) (w.length+1)
      (wordState exit (tape (w.reverse.map some++l) []) m p ((w.map digit).reverse++buf) out) := by
  induction w generalizing l buf with
  | nil=>
    simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.map_nil,List.nil_append] using
      uniform_step _ _ _ (read_empty C A q exit h l m p buf out)
  | cons b w ih=>
    have hs:=uniform_step _ _ _ (read_step C A q exit h l b w m p buf out)
    have hi:=ih (some b::l) (digit b::buf)
    convert hs.trans hi using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.map_append,
        List.map_cons,List.append_assoc,List.singleton_append,List.map_nil]; try omega)

theorem buf_step (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (a : Fin g) (xs m p : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p (a::xs) out) coin=
      wordState q i (a::m) p xs out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,List.head?_cons,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem buf_empty (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (m p : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p [] out) coin=
      wordState exit i m p [] out y := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,List.head?_nil,pass,BitTape.shift]
  rfl

theorem buf_run (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (xs m p : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q i m p xs out) (xs.length+1)
      (wordState exit i (xs.reverse++m) p [] out y) := by
  induction xs generalizing m with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      uniform_step _ _ _ (buf_empty C A q exit y h i m p out)
  | cons a xs ih=>
    have hs:=uniform_step _ _ _ (buf_step C A q exit y h i a xs m p out)
    convert hs.trans (ih (a::m)) using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]; try omega)

theorem pay_step (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=drain q exit .pay hd)
    (i : BitTape) (a : Fin g) (xs m b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m (a::xs) b out) coin=
      wordState q i (a::m) xs b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,drain,List.head?_cons,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem pay_empty (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=drain q exit .pay hd)
    (i : BitTape) (m b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m [] b out) coin=
      wordState exit i m [] b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,drain,List.head?_nil,pass,BitTape.shift]
  rfl

theorem pay_run (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=drain q exit .pay hd)
    (i : BitTape) (xs m b : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q i m xs b out) (xs.length+1)
      (wordState exit i (xs.reverse++m) [] b out) := by
  induction xs generalizing m with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      uniform_step _ _ _ (pay_empty C A q exit h i m b out)
  | cons a xs ih=>
    have hs:=uniform_step _ _ _ (pay_step C A q exit h i a xs m b out)
    convert hs.trans (ih (a::m)) using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]; try omega)

end UniformKServer.UniformWrapper

end

end OAI
