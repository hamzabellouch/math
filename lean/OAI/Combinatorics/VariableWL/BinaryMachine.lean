import OAI.Combinatorics.VariableWL.UnaryPower

namespace OAI

namespace VariableWL.Computation.Stack.BinaryMachine
open Code

def store (w : Word) (q : ℕ) : Stores 3 :=
  fun i => if i=0 then w else if i=1 then List.replicate q true else []

 theorem update_input (w v : Word) (q : ℕ) :
    Function.update (store w q) 0 v=store v q := by
  funext i
  fin_cases i <;> simp [store]

 theorem update_accumulator (w : Word) (q n : ℕ) :
    Function.update (store w q) 1 (List.replicate n true)=store w n := by
  funext i
  fin_cases i <;> simp [store]

def double : Code 3 := .seq (duplicate 1 2 3 (fun _ => true)) (transfer 3 1 id)

 theorem eval_double (w : Word) (q : ℕ) :
    Eval double (store w q) (9*q+2) (store w (2*q)) := by
  have hd := eval_length_add (k := 3) 1 2 3 (by decide) (by decide) (by decide)
    (store w q) (by simp [store]) 0 (by simp [store])
  simp only [store,show (1:Fin 4)≠0 by decide,ite_false,ite_true,List.length_replicate,Nat.add_zero] at hd
  let s := Function.update (store w q) 3 (List.replicate q true)
  have ht := eval_transfer (k := 3) 3 1 (by decide) id s
  have h3 : s 3=List.replicate q true := by simp [s]
  have h1 : s 1=List.replicate q true := by simp [s,store]
  rw [h3,h1] at ht
  simp only [List.length_replicate,List.reverse_replicate,List.map_id_fun,id_eq,← List.replicate_add] at ht
  have hs : pairStore s 3 1 [] (List.replicate (q+q) true)=store w (2*q) := by
    funext i
    fin_cases i <;> simp [s,pairStore,store,two_mul]
  rw [hs] at ht
  have he := Eval.seq hd ht
  have hn : 9*q+2=(6*q+1)+1+3*q := by omega
  rw [hn]
  exact he

def addBit : Code 3 := .branch (fun h => (h 0).getD false) (push 1 true) .skip

 theorem eval_addBit (b : Bool) (w : Word) (q : ℕ) :
    Eval addBit (store (b::w) q) (1+b.toNat) (store (b::w) (q+b.toNat)) := by
  cases b with
  | false =>
    simpa only [addBit,Bool.toNat_false,Nat.add_zero,Nat.zero_add] using
      (Eval.branch_false (p := fun h => (h 0).getD false) (a := push 1 true)
        (by simp [heads,store]) (Eval.skip (store (false::w) q)))
  | true =>
    have hp := eval_push (k := 3) 1 true (store (true::w) q)
    have hu : Function.update (store (true::w) q) 1 (true::store (true::w) q 1)=
        store (true::w) (q+1) := by
      rw [show store (true::w) q 1=List.replicate q true by simp [store],← List.replicate_succ]
      exact update_accumulator _ _ _
    rw [hu] at hp
    exact Eval.branch_true (by simp [heads,store]) hp

def body : Code 3 := .seq double (.seq addBit (pop 0))

 theorem eval_body (b : Bool) (w : Word) (q : ℕ) :
    Eval body (store (b::w) q) (9*q+6+b.toNat) (store w (2*q+b.toNat)) := by
  have hp := eval_pop (k := 3) 0 (store (b::w) (2*q+b.toNat))
  simp only [store,ite_true,List.tail_cons] at hp
  rw [update_input] at hp
  have he := Eval.seq (eval_double (b::w) q) (Eval.seq (eval_addBit b w (2*q)) hp)
  have hn : 9*q+6+b.toNat=(9*q+2)+1+((1+b.toNat)+1+1) := by omega
  rw [hn]
  exact he

def program : Code 3 := .loop (fun h => (h 0).isSome) body

def value : Word → ℕ → ℕ
  | [],q => q
  | b::w,q => value w (2*q+b.toNat)

def time : Word → ℕ → ℕ
  | [],_ => 0
  | b::w,q => (9*q+8+b.toNat)+time w (2*q+b.toNat)

 theorem eval_program (w : Word) (q : ℕ) :
    Eval program (store w q) (time w q) (store [] (value w q)) := by
  induction w generalizing q with
  | nil => exact Eval.loop_false (by simp [heads,store])
  | cons b w ih =>
    have he := Eval.loop_true (p := fun h => (h 0).isSome)
      (by simp [heads,store]) (eval_body b w q) (ih (2*q+b.toNat))
    have hn : time (b::w) q=(9*q+6+b.toNat)+2+time w (2*q+b.toNat) := by simp only [time]; omega
    rw [hn]
    exact he

 theorem value_bound (w : Word) (q : ℕ) : value w q+1 ≤ (q+1)*2^w.length := by
  induction w generalizing q with
  | nil => simp [value]
  | cons b w ih =>
    have h := ih (2*q+b.toNat)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    simp only [value,List.length_cons,pow_succ]
    nlinarith [Nat.mul_le_mul_right (2^w.length) (show 2*q+b.toNat+1 ≤ 2*(q+1) by omega)]

 theorem time_bound (w : Word) (q : ℕ) : time w q ≤ 9*(q+1)*(2^w.length-1) := by
  induction w generalizing q with
  | nil => simp [time]
  | cons b w ih =>
    have h := ih (2*q+b.toNat)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    have hp : 1 ≤ 2^w.length := Nat.one_le_two_pow
    have hp' : 2^w.length-1+1=2^w.length := by omega
    simp only [time,List.length_cons,pow_succ]
    have hcoef : 9*(2*q+b.toNat+1)*(2^w.length-1) ≤ 18*(q+1)*(2^w.length-1) := by
      calc
        _ ≤ 9*(2*(q+1))*(2^w.length-1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 9 (by omega))
        _ = _ := by ring
    have he : 2^w.length*2-1=2*(2^w.length-1)+1 := by omega
    rw [he]
    nlinarith

 theorem value_append (u v : Word) (q : ℕ) : value (u++v) q=value v (value u q) := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => exact ih (2*q+b.toNat)

 theorem value_reverse (w : Word) (q : ℕ) : value w.reverse q=q*2^w.length+Encoding.value w := by
  induction w generalizing q with
  | nil => simp [value,Encoding.value]
  | cons b w ih =>
    rw [List.reverse_cons,value_append,ih]
    simp only [value,List.length_cons,pow_succ,Encoding.value,List.foldr_cons]
    cases b <;> simp [Nat.bit] <;> ring

noncomputable def machine : VariableWL.Machine := (program.machine 1).compile

 theorem outputs (w : Word) : VariableWL.OutputsWithin machine w
    (List.replicate (Encoding.value w) true) (44*2^w.length) := by
  have he := eval_program w.reverse 0
  have hin : store w.reverse 0=(fun j => if j=0 then w.reverse else []) := by
    funext j
    simp [store]
  rw [hin] at he
  have hh := eval_outputs program 1 w he
  have hout : store [] (value w.reverse 0) 1=List.replicate (Encoding.value w) true := by
    simp [store,value_reverse]
  rw [hout] at hh
  obtain ⟨t,ht,hh,ho⟩ := hh
  have hb := time_bound w.reverse 0
  simp only [List.length_reverse,Nat.zero_add,Nat.mul_one] at hb
  have hm : w.length ≤ 2^w.length := Nat.le_of_lt Nat.lt_two_pow_self
  refine ⟨t,ht.trans ?_,hh,ho⟩
  have hs : 2^w.length-1+1=2^w.length := Nat.sub_add_cancel Nat.one_le_two_pow
  nlinarith

end VariableWL.Computation.Stack.BinaryMachine

namespace VariableWL.Computation.Stack.ArrayLookup
open Code

def store (w : Word) (n : ℕ) (v out : Word) : Stores 4 :=
  fun i => if i=0 then w else if i=1 then List.replicate n true
  else if i=2 then v else if i=4 then out else []

 theorem update_query (w v u out : Word) (n : ℕ) :
    Function.update (store w n v out) 2 u=store w n u out := by
  funext i
  fin_cases i <;> simp [store]

 theorem update_output (w v out u : Word) (n : ℕ) :
    Function.update (store w n v out) 4 u=store w n v u := by
  funext i
  fin_cases i <;> simp [store]

def clone : Code 4 := .seq (duplicate 0 2 3 id) (transfer 3 2 id)

 theorem eval_clone (w : Word) (n : ℕ) (out : Word) :
    Eval clone (store w n [] out) (9*w.length+2) (store w n w out) := by
  have hd := eval_duplicate (k := 4) 0 2 3 (by decide) (by decide) (by decide)
    id (store w n [] out) (by simp [store])
  simp only [store,ite_true,List.map_id_fun,id_eq,show (3:Fin 5)≠0 by decide,
    show (3:Fin 5)≠1 by decide,show (3:Fin 5)≠2 by decide,show (3:Fin 5)≠4 by decide,
    ite_false,List.append_nil] at hd
  let s := Function.update (store w n [] out) 3 w.reverse
  have ht := eval_transfer (k := 4) 3 2 (by decide) id s
  have h3 : s 3=w.reverse := by simp [s]
  have h2 : s 2=[] := by simp [s,store]
  rw [h3,h2] at ht
  simp only [List.reverse_reverse,List.length_reverse,List.map_id_fun,id_eq,List.append_nil] at ht
  have hs : pairStore s 3 2 [] w=store w n w out := by
    funext i
    fin_cases i <;> simp [pairStore,s,store]
  rw [hs] at ht
  have hn : 9*w.length+2=(6*w.length+1)+1+3*w.length := by omega
  rw [hn]
  exact Eval.seq hd ht

def scan : Code 4 := .loop (fun h => (h 1).isSome)
  (.action fun _ i => if i=1 ∨ i=2 then .pop else .keep)

 theorem scan_action (w v out : Word) (n : ℕ) :
    execute (fun i => if i=1 ∨ i=2 then .pop else .keep) (store w (n+1) v out)=
      store w n v.tail out := by
  funext i
  fin_cases i <;> simp [execute,store,Action.apply,List.replicate_succ]

 theorem eval_scan (w v out : Word) (n : ℕ) :
    Eval scan (store w n v out) (3*n) (store w 0 (v.drop n) out) := by
  induction n generalizing v with
  | zero =>
    exact Eval.loop_false (p := fun h => (h 1).isSome) (by simp [heads,store])
  | succ n ih =>
    have ha := Eval.action (fun (_ : Heads 4) i => if i=1 ∨ i=2 then .pop else .keep)
      (store w (n+1) v out)
    rw [scan_action] at ha
    have he := Eval.loop_true (p := fun h => (h 1).isSome)
      (by simp [heads,store,List.replicate_succ]) ha (ih v.tail)
    have hn : 3*(n+1)=1+2+3*n := by omega
    rw [hn,show v.drop (n+1)=v.tail.drop n by cases v <;> simp]
    exact he

def readHead : Code 4 := .action fun h => one 4 (.push ((h 2).getD false))

 theorem eval_readHead (w v out : Word) (n : ℕ) :
    Eval readHead (store w n v out) 1 (store w n v (v.head?.getD false::out)) := by
  have h := Eval.action (fun h : Heads 4 => one 4 (.push ((h 2).getD false))) (store w n v out)
  simp only [execute_one] at h
  have he : (heads (store w n v out) 2).getD false=v.head?.getD false := by simp [heads,store]
  rw [he] at h
  change Eval _ _ _ (Function.update (store w n v out) 4 (v.head?.getD false::store w n v out 4)) at h
  rw [show store w n v out 4=out by simp [store],update_output] at h
  exact h

def program : Code 4 := .seq clone (.seq scan (.seq readHead (clear 2)))

 theorem eval_program (w out : Word) (n : ℕ) :
    Eval program (store w n [] out) (9*w.length+3*n+3*(w.drop n).length+6)
      (store w 0 [] (w.getD n false::out)) := by
  have hc := eval_clear (k := 4) 2 (store w 0 (w.drop n) ((w.drop n).head?.getD false::out))
  rw [show store w 0 (w.drop n) ((w.drop n).head?.getD false::out) 2=w.drop n by simp [store],
    update_query] at hc
  have he := Eval.seq (eval_clone w n out)
    (Eval.seq (eval_scan w w out n) (Eval.seq (eval_readHead w (w.drop n) out 0) hc))
  have hn : 9*w.length+3*n+3*(w.drop n).length+6=
      (9*w.length+2)+1+(3*n+1+(1+1+3*(w.drop n).length)) := by omega
  rw [hn]
  have hh : (w.drop n).head?.getD false=w.getD n false := by
    rw [List.head?_drop]
    rfl
  simpa only [program,hh] using he

 theorem time_bound (w : Word) (n : ℕ) :
    9*w.length+3*n+3*(w.drop n).length+6 ≤ 12*(w.length+n+1) := by
  rw [List.length_drop]
  omega

end VariableWL.Computation.Stack.ArrayLookup

namespace VariableWL.Computation.Stack.Halving
open Code

def store (n q r : ℕ) : Stores 2 :=
  fun i => if i=0 then List.replicate n true else if i=1 then List.replicate q true
  else List.replicate r true

def pair : Code 2 := .action fun _ i =>
  if i=0 then .pop else if i=1 then .push true else .keep

def body : Code 2 := .seq (pop 0) (.branch (fun h => (h 0).isSome) pair (push 2 true))

def program : Code 2 := .loop (fun h => (h 0).isSome) body

 theorem eval_pop_first (n q r : ℕ) :
    Eval (pop (k := 2) 0) (store (n+1) q r) 1 (store n q r) := by
  have h := eval_pop (k := 2) 0 (store (n+1) q r)
  have he : Function.update (store (n+1) q r) 0 ((store (n+1) q r 0).tail)=store n q r := by
    funext i
    fin_cases i <;> simp [store,List.replicate_succ]
  rw [he] at h
  exact h

 theorem eval_pair (n q r : ℕ) : Eval pair (store (n+1) q r) 1 (store n (q+1) r) := by
  have he := Eval.action (fun (_ : Heads 2) i => if i=0 then .pop else if i=1 then .push true else .keep)
    (store (n+1) q r)
  have hs : execute (fun i => if i=0 then .pop else if i=1 then .push true else .keep)
      (store (n+1) q r)=store n (q+1) r := by
    funext i
    fin_cases i <;> simp [execute,store,Action.apply,List.replicate_succ]
  rw [hs] at he
  exact he

 theorem eval_last (q r : ℕ) : Eval (push (k := 2) 2 true) (store 0 q r) 1 (store 0 q (r+1)) := by
  have he := eval_push (k := 2) 2 true (store 0 q r)
  have hs : Function.update (store 0 q r) 2 (true::store 0 q r 2)=store 0 q (r+1) := by
    funext i
    fin_cases i <;> simp [store,List.replicate_succ]
  rw [hs] at he
  exact he

 theorem eval_body_pair (n q r : ℕ) : Eval body (store (n+2) q r) 4 (store n (q+1) r) := by
  have hb := Eval.branch_true (p := fun h : Heads 2 => (h 0).isSome)
    (b := push 2 true) (by simp [heads,store,List.replicate_succ]) (eval_pair n q r)
  exact Eval.seq (eval_pop_first (n+1) q r) hb

 theorem eval_body_last (q r : ℕ) : Eval body (store 1 q r) 4 (store 0 q (r+1)) := by
  have hb := Eval.branch_false (p := fun h : Heads 2 => (h 0).isSome)
    (a := pair) (by simp [heads,store]) (eval_last q r)
  exact Eval.seq (eval_pop_first 0 q r) hb

 theorem eval_program (n q r : ℕ) :
    Eval program (store n q r) (6*((n+1)/2)) (store 0 (q+n/2) (r+n%2)) := by
  induction n using Nat.twoStepInduction generalizing q r with
  | zero =>
    simpa only [program,Nat.zero_add,Nat.reduceDiv,Nat.mul_zero,Nat.zero_div,Nat.zero_mod,Nat.add_zero] using
      (Eval.loop_false (p := fun h : Heads 2 => (h 0).isSome) (a := body)
        (s := store 0 q r) (by simp [heads,store]))
  | one =>
    have hz := Eval.loop_false (p := fun h : Heads 2 => (h 0).isSome) (a := body)
      (s := store 0 q (r+1)) (by simp [heads,store])
    have he := Eval.loop_true (p := fun h : Heads 2 => (h 0).isSome)
      (by simp [heads,store]) (eval_body_last q r) hz
    simpa only [program,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMod,Nat.add_zero,Nat.reduceMul] using he
  | more n ih _ =>
    have he := Eval.loop_true (p := fun h : Heads 2 => (h 0).isSome)
      (by simp [heads,store,List.replicate_succ]) (eval_body_pair n q r) (ih (q+1) r)
    have ht : 6*((n+2+1)/2)=4+2+6*((n+1)/2) := by omega
    have hq : q+(n+2)/2=q+1+n/2 := by omega
    have hr : r+(n+2)%2=r+n%2 := by omega
    rw [ht,hq,hr]
    exact he

 theorem time_bound (n : ℕ) : 6*((n+1)/2) ≤ 6*n := by omega

end VariableWL.Computation.Stack.Halving

end OAI
