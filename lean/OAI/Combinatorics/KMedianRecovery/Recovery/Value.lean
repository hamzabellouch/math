import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.ExtractPrefix

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

def sumBit (c x y : Bool) : Bool := xor (xor c x) y
def carryBit (c x y : Bool) : Bool := (c && x) || (c && y) || (x && y)

lemma fullAdder (c x y : Bool) :
    (sumBit c x y).toNat+2*(carryBit c x y).toNat=c.toNat+x.toNat+y.toNat := by
  cases c <;> cases x <;> cases y <;> rfl

def add : Bool → List Bool → List Bool → List Bool
  | c,[],[] => if c then [true] else []
  | c,x::xs,[] => sumBit c x false :: add (carryBit c x false) xs []
  | c,[],y::ys => sumBit c false y :: add (carryBit c false y) [] ys
  | c,x::xs,y::ys => sumBit c x y :: add (carryBit c x y) xs ys
termination_by _ xs ys => xs.length+ys.length

lemma value_add (c : Bool) (xs ys : List Bool) :
    value (add c xs ys)=value xs+value ys+c.toNat := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [add,value]
    | cons y ys ih =>
      simp only [add,value,ih]
      have he := fullAdder c false y
      simp only [Bool.toNat_false] at he
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [add,value,ih]
      have he := fullAdder c x false
      simp only [Bool.toNat_false] at he
      omega
    | cons y ys =>
      simp only [add,value,ih]
      have he := fullAdder c x y
      omega

lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h,value,ih]
    cases b <;> simp [Nat.bit,Nat.add_comm]

def triStacks (x y z : List Bool) : Stacks (Fin 3) := ![x,y,z]

@[simp] lemma stacks_zero (x y z : List Bool) : triStacks x y z 0=x := rfl
@[simp] lemma stacks_one (x y z : List Bool) : triStacks x y z 1=y := rfl
@[simp] lemma stacks_two (x y z : List Bool) : triStacks x y z 2=z := rfl

lemma update_zero (x y z t : List Bool) :
    Function.update (triStacks x y z) 0 t=triStacks t y z := by
  funext i
  fin_cases i <;> simp [triStacks]
lemma update_one (x y z t : List Bool) :
    Function.update (triStacks x y z) 1 t=triStacks x t z := by
  funext i
  fin_cases i <;> simp [triStacks]
lemma update_two (x y z t : List Bool) :
    Function.update (triStacks x y z) 2 t=triStacks x y t := by
  funext i
  fin_cases i <;> simp [triStacks]

abbrev addProgram : Program where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 3
  main := 0
  State := Bool × Option Bool × Option Bool
  initial := (false,none,none)
  code l := if l=0 then
    .pop 0 (fun s b => (s.1,b,none))
      (.branch (fun s => decide (s.2.1=some true))
        (.pop 0 (fun s b => (s.1,b,none))
          (.branch (fun s => s.2.1.isSome)
            (.push 1 (fun s => s.2.1.getD false)
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 0))))
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 1)))))
        (.load (fun _ => (false,none,none)) (.goto (fun _ => 1))))
    else if l=1 then
      .pop 1 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.push 2 (fun s => s.2.1.getD false)
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 1))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 2))))
    else
      .pop 2 (fun s b => (s.1,b,none))
        (.pop 0 (fun s b => (s.1,s.2.1,b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.push 1 (fun s => sumBit s.1 (s.2.1.getD false) (s.2.2.getD false))
              (.load (fun s => (carryBit s.1 (s.2.1.getD false) (s.2.2.getD false),none,none))
                (.goto (fun _ => 2))))
            (.branch Prod.fst
              (.push 1 (fun _ => true) (.load (fun _ => (false,none,none)) .halt))
              (.load (fun _ => (false,none,none)) .halt))))

def cfg (l : Fin 3) (c : Bool) (x y z : List Bool) : addProgram.machine.Cfg :=
  ⟨some l,(c,none,none),triStacks x y z⟩
def done (ys : List Bool) : addProgram.machine.Cfg :=
  ⟨none,(false,none,none),triStacks [] ys []⟩

lemma add_initial (xs : List Bool) : initList addProgram.machine xs=cfg 0 false xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [addProgram,triStacks]

lemma add_final (xs : List Bool) : haltList addProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [addProgram,triStacks]

lemma parse_nil (ys : List Bool) :
    addProgram.machine.step (cfg 0 false [] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_one (ys : List Bool) :
    addProgram.machine.step (cfg 0 false [true] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_false (xs ys : List Bool) :
    addProgram.machine.step (cfg 0 false (false::xs) ys [])=some (cfg 1 false xs ys []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    addProgram.machine.step (cfg 0 false (true::b::xs) ys [])=some (cfg 0 false xs (b::ys) []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_one]
  rfl

lemma rev_nil (xs zs : List Bool) :
    addProgram.machine.step (cfg 1 false xs [] zs)=some (cfg 2 false xs [] zs) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_one]
  rfl
lemma rev_cons (b : Bool) (xs ys zs : List Bool) :
    addProgram.machine.step (cfg 1 false xs (b::ys) zs)=some (cfg 1 false xs ys (b::zs)) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_one,update_two]
  rfl

lemma sum_nil (c : Bool) (zs : List Bool) :
    addProgram.machine.step (cfg 2 c [] zs [])=some (done ((if c then [true] else [])++zs)) := by
  cases c <;> simp [FinTM2.step,cfg,done,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  all_goals rfl

lemma sum_cons_nil (c x : Bool) (xs zs : List Bool) :
    addProgram.machine.step (cfg 2 c [] zs (x::xs))=
      some (cfg 2 (carryBit c x false) [] (sumBit c x false::zs) xs) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_nil_cons (c y : Bool) (ys zs : List Bool) :
    addProgram.machine.step (cfg 2 c (y::ys) zs [])=
      some (cfg 2 (carryBit c false y) ys (sumBit c false y::zs) []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_cons_cons (c x y : Bool) (xs ys zs : List Bool) :
    addProgram.machine.step (cfg 2 c (y::ys) zs (x::xs))=
      some (cfg 2 (carryBit c x y) ys (sumBit c x y::zs) xs) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl

noncomputable def sum_outputs (c : Bool) (xs ys zs : List Bool) :
    EvalsToInTime addProgram.machine.step (cfg 2 c ys zs xs)
      (some (done ((add c xs ys).reverse++zs))) (xs.length+ys.length+1) := by
  induction xs generalizing c ys zs with
  | nil =>
    induction ys generalizing c zs with
    | nil =>
      cases c with
      | false => simpa [add] using one_step (sum_nil false zs)
      | true => simpa [add] using one_step (sum_nil true zs)
    | cons y ys ih =>
      have hh := step_then (sum_nil_cons c y ys zs) (ih (carryBit c false y) (sumBit c false y::zs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
        List.length_nil,Nat.zero_add] using hh
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hh := step_then (sum_cons_nil c x xs zs) (ih (carryBit c x false) [] (sumBit c x false::zs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
        List.length_nil,Nat.add_zero] using hh
    | cons y ys =>
      have hh := step_then (sum_cons_cons c x y xs ys zs) (ih (carryBit c x y) ys (sumBit c x y::zs))
      simp only [add,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp; omega)

noncomputable def rev_outputs (xs ys zs : List Bool) :
    EvalsToInTime addProgram.machine.step (cfg 1 false xs ys zs)
      (some (done ((add false (ys.reverse++zs) xs).reverse)))
        (ys.length+(ys.length+zs.length)+xs.length+2) := by
  induction ys generalizing zs with
  | nil =>
    have hh := step_then (rev_nil xs zs) (sum_outputs false zs xs [])
    simpa only [List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,Nat.add_assoc]
      using hh
  | cons b ys ih =>
    have hh := step_then (rev_cons b xs ys zs) (ih (b::zs))
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
    exact time_mono hh (by simp; omega)

noncomputable def parse_outputs (xs ys : List Bool) :
    EvalsToInTime addProgram.machine.step (cfg 0 false xs ys [])
      (some (done ((add false ((extractPrefix xs).reverse++ys).reverse (discardPrefix xs)).reverse)))
        (2*xs.length+2*ys.length+3) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil =>
    have hh := step_then (parse_nil ys) (rev_outputs [] ys [])
    simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,
      List.length_nil,Nat.add_zero,Nat.zero_add] using time_mono hh (by simp; omega)
  | singleton b =>
    cases b with
    | false =>
      have hh := step_then (parse_false [] ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp; omega)
    | true =>
      have hh := step_then (parse_one ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp; omega)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      have hh := step_then (parse_false (c::xs) ys) (rev_outputs (c::xs) ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil] using
        time_mono hh (by simp; omega)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp; omega)

noncomputable def addReverse_computes : PolyComputes (fun xs =>
    (add false (extractPrefix xs) (discardPrefix xs)).reverse) where
  program := addProgram
  time := 2*Polynomial.X+3
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,add_initial,add_final,List.append_nil,
      List.reverse_reverse,List.length_nil,Nat.mul_zero,Nat.add_zero,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using parse_outputs xs []

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
