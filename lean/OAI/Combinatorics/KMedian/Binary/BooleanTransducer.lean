import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanPolynomial

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure Transducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × List Bool
  finish : Q → List Bool
attribute [instance] Transducer.finiteQ

namespace Transducer
variable (T : Transducer)

def run : T.Q → List Bool → List Bool
  | q, [] => T.finish q
  | q, b::xs => (T.next q b).2 ++ run (T.next q b).1 xs

def width : ℕ := max (univ.sup (fun q => (T.finish q).length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.length))

 theorem finish_length (q : T.Q) : (T.finish q).length ≤ T.width :=
  (le_sup (f:=fun q => (T.finish q).length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) : (T.next q b).2.length ≤ T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.length) (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) : (T.run q xs).length ≤ T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

inductive Key | input | buffer | output deriving DecidableEq
instance : Fintype Key := ⟨{Key.input,Key.buffer,Key.output},by
  intro k
  cases k <;> simp⟩
open Key
abbrev Label := T.Q ⊕ Unit
abbrev State := Option Bool

def emit : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], q => q
  | b::bs, q => .push buffer (fun _ => b) (emit bs q)

 theorem emit_step (bits : List Bool) (q : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (s : Key → List Bool) :
    TM2.stepAux (emit T bits q) v s=
      TM2.stepAux q v (update s buffer (bits.reverse++s buffer)) := by
  induction bits generalizing s with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons]
      simp only [List.append_assoc,List.singleton_append]

def transfer : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop buffer (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr ()))))
      (.load (fun _ => none) .halt))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emit T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emit T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emit T (T.finish q) (.goto (fun _ => .inr ())))))
  | .inr _ => transfer T

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def store (xs ys zs : List Bool) : Key → List Bool
  | input => xs
  | buffer => ys
  | output => zs

 theorem stacks_update_input (xs ys zs ts : List Bool) :
    update (store xs ys zs) input ts=store ts ys zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_buffer (xs ys zs ts : List Bool) :
    update (store xs ys zs) buffer ts=store xs ts zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_output (xs ys zs ts : List Bool) :
    update (store xs ys zs) output ts=store xs ys ts := by
  funext k
  cases k <;> simp [store]

def readCfg (q : T.Q) (xs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ys []⟩

def transferCfg (ys zs : List Bool) : (machine T).Cfg :=
  ⟨some (.inr ()),none,store [] ys zs⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ys : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ys)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.reverse++ys)) := by
  cases b <;>
    simp [readCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
      emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_nil (q : T.Q) (ys : List Bool) :
    (machine T).step (T.readCfg q [] ys)=some (T.transferCfg ((T.finish q).reverse++ys) []) := by
  simp [readCfg,transferCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
    emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_run (q : T.Q) (xs ys : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ys)
      (T.transferCfg ((T.run q xs).reverse++ys) []) := by
  induction xs generalizing q ys with
  | nil => exact Trace.cons (T.read_nil q ys) (Trace.refl _)
  | cons b xs ih =>
      have h := Trace.cons (T.read_cons q b xs ys) (ih (T.next q b).1 ((T.next q b).2.reverse++ys))
      simpa only [run,List.reverse_append,List.append_assoc,List.length_cons] using h

 theorem transfer_cons (b : Bool) (ys zs : List Bool) :
    (machine T).step (T.transferCfg (b::ys) zs)=some (T.transferCfg ys (b::zs)) := by
  simp [transferCfg,TM2.step,code,transfer,TM2.stepAux,store,List.head?,List.tail,
    stacks_update_buffer,stacks_update_output]

 theorem transfer_nil (zs : List Bool) :
    (machine T).step (T.transferCfg [] zs)=some ((machine T).finalCfg zs) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store]

 theorem transfer_run (ys zs : List Bool) :
    Trace (machine T).step (ys.length+1) (T.transferCfg ys zs)
      ((machine T).finalCfg (ys.reverse++zs)) := by
  induction ys generalizing zs with
  | nil => exact Trace.cons (T.transfer_nil zs) (Trace.refl _)
  | cons b ys ih =>
      have h := Trace.cons (T.transfer_cons b ys zs) (ih (b::zs))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).length+2)
      ((machine T).initialCfg xs) ((machine T).finalCfg (T.run T.initial xs)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] := by
    apply cfg_ext <;> try rfl
    funext k
    cases k <;> simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have hr := T.read_run T.initial xs []
  simp only [List.append_nil] at hr
  have h := hr.trans (T.transfer_run (T.run T.initial xs).reverse [])
  simpa only [List.append_nil,List.length_reverse,List.reverse_reverse,
    show xs.length+1+((T.run T.initial xs).length+1)=xs.length+(T.run T.initial xs).length+2 by omega] using h

noncomputable def program : PolyProgram id id (T.run T.initial) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+2)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end Transducer
end MetricKMedian.Binary
end

end OAI
