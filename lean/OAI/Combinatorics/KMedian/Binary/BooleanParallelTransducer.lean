import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanPolynomial

namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure ParallelTransducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × (List Bool × List Bool)
  finish : Q → List Bool × List Bool
attribute [instance] ParallelTransducer.finiteQ

namespace ParallelTransducer
variable (T : ParallelTransducer)

def run : T.Q → List Bool → List Bool × List Bool
  | q, [] => T.finish q
  | q, b::xs =>
    let v := T.next q b
    let z := run v.1 xs
    (v.2.1++z.1,v.2.2++z.2)

def width : ℕ := max (univ.sup (fun q => (T.finish q).1.length+(T.finish q).2.length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length))

 theorem finish_length (q : T.Q) : (T.finish q).1.length+(T.finish q).2.length≤T.width :=
  (le_sup (f:=fun q => (T.finish q).1.length+(T.finish q).2.length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) :
    (T.next q b).2.1.length+(T.next q b).2.2.length≤T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length)
    (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) :
    (T.run q xs).1.length+(T.run q xs).2.length≤T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

abbrev Key := Fin 4
abbrev input : Key := 0
abbrev left : Key := 1
abbrev right : Key := 2
abbrev output : Key := 3
abbrev Label := T.Q ⊕ Bool
abbrev State := Option Bool

def store (xs ls rs ys : List Bool) : Key → List Bool :=
  fun k => if k=input then xs else if k=left then ls else if k=right then rs else ys

 theorem store_update_input (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) input zs=store zs ls rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_left (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) left zs=store xs zs rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_right (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) right zs=store xs ls zs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_output (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) output zs=store xs ls rs zs := by
  funext k
  fin_cases k <;> simp [store,input,left,right,output]

def emit (k : Key) : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], s => s
  | b::bs, s => .push k (fun _ => b) (emit k bs s)

 theorem emit_step (k : Key) (bits : List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (stk : Key → List Bool) :
    TM2.stepAux (emit T k bits s) v stk=TM2.stepAux s v (update stk k (bits.reverse++stk k)) := by
  induction bits generalizing stk with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons,
        List.append_assoc,List.singleton_append]

def emitPair (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State) :=
  emit T left p.1 (emit T right p.2 s)

 theorem emitPair_step (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (xs ls rs ys : List Bool) :
    TM2.stepAux (emitPair T p s) v (store xs ls rs ys)=
      TM2.stepAux s v (store xs (p.1.reverse++ls) (p.2.reverse++rs) ys) := by
  simp [emitPair,emit_step,store,input,left,right,store_update_left,store_update_right]

def transfer (phase : Bool) : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop (if phase then left else right) (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr phase))))
      (.load (fun _ => none) (if phase then .halt else .goto (fun _ => .inr true))))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emitPair T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emitPair T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emitPair T (T.finish q) (.goto (fun _ => .inr false)))))
  | .inr b => transfer T b

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def readCfg (q : T.Q) (xs ls rs : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ls rs []⟩
def rightCfg (ls rs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr false),none,store [] ls rs ys⟩
def leftCfg (ls ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr true),none,store [] ls [] ys⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ls rs : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ls rs)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs)) := by
  cases b <;> simp [readCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_nil (q : T.Q) (ls rs : List Bool) :
    (machine T).step (T.readCfg q [] ls rs)=
      some (T.rightCfg ((T.finish q).1.reverse++ls) ((T.finish q).2.reverse++rs) []) := by
  simp [readCfg,rightCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_run (q : T.Q) (xs ls rs : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ls rs)
      (T.rightCfg ((T.run q xs).1.reverse++ls) ((T.run q xs).2.reverse++rs) []) := by
  induction xs generalizing q ls rs with
  | nil => exact Trace.cons (T.read_nil q ls rs) (Trace.refl _)
  | cons b xs ih =>
      simpa only [run,List.length_cons,List.reverse_append,List.append_assoc] using
        Trace.cons (T.read_cons q b xs ls rs)
          (ih (T.next q b).1 ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs))

 theorem right_cons (b : Bool) (ls rs ys : List Bool) :
    (machine T).step (T.rightCfg ls (b::rs) ys)=some (T.rightCfg ls rs (b::ys)) := by
  simp [rightCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right,store_update_output]

 theorem right_nil (ls ys : List Bool) :
    (machine T).step (T.rightCfg ls [] ys)=some (T.leftCfg ls ys) := by
  simp [rightCfg,leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right]

 theorem right_run (ls rs ys : List Bool) :
    Trace (machine T).step (rs.length+1) (T.rightCfg ls rs ys) (T.leftCfg ls (rs.reverse++ys)) := by
  induction rs generalizing ys with
  | nil => exact Trace.cons (T.right_nil ls ys) (Trace.refl _)
  | cons b rs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.right_cons b ls rs ys) (ih (b::ys))

 theorem left_cons (b : Bool) (ls ys : List Bool) :
    (machine T).step (T.leftCfg (b::ls) ys)=some (T.leftCfg ls (b::ys)) := by
  simp [leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_left,store_update_output]

 theorem left_nil (ys : List Bool) :
    (machine T).step (T.leftCfg [] ys)=some ((machine T).finalCfg ys) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    fin_cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store,input,left,right,output]

 theorem left_run (ls ys : List Bool) :
    Trace (machine T).step (ls.length+1) (T.leftCfg ls ys) ((machine T).finalCfg (ls.reverse++ys)) := by
  induction ls generalizing ys with
  | nil => exact Trace.cons (T.left_nil ys) (Trace.refl _)
  | cons b ls ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.left_cons b ls ys) (ih (b::ys))

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).1.length+(T.run T.initial xs).2.length+3)
      ((machine T).initialCfg xs)
      ((machine T).finalCfg ((T.run T.initial xs).1++(T.run T.initial xs).2)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] [] := by
    apply cfg_ext <;> try rfl
    funext k
    fin_cases k <;> simp [Machine.initialCfg,readCfg,store,input,left,right]
  rw [hi]
  have hr := T.read_run T.initial xs [] []
  simp only [List.append_nil] at hr
  have hs := T.right_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2.reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hs
  have ht := T.left_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2
  simp only [List.length_reverse,List.reverse_reverse] at ht
  have h := (hr.trans hs).trans ht
  convert h using 1
  omega

noncomputable def program : PolyProgram id id (fun xs => (T.run T.initial xs).1++(T.run T.initial xs).2) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+3)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI
