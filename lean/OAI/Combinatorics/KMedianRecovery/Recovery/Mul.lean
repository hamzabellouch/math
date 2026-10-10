import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EvalTrans
import OAI.Combinatorics.KMedianRecovery.Recovery.Normalize

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

lemma add_length (c : Bool) (xs ys : List Bool) :
    (add c xs ys).length≤xs.length+ys.length+1 := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [add]
    | cons y ys ih => simp only [add,List.length_cons,List.length_nil] at ⊢; have hh:=ih (carryBit c false y); simp only [List.length_nil] at hh; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [add,List.length_cons,List.length_nil] at ⊢; have hh:=ih (carryBit c x false) []; simp only [List.length_nil] at hh; omega
    | cons y ys => simp only [add,List.length_cons]; have hh:=ih (carryBit c x y) ys; omega

def mulFrom : List Bool → List Bool → List Bool → List Bool
  | [],_,acc => acc
  | b::bs,ys,acc => mulFrom bs ys (if b then add false ys (false::acc) else false::acc)

lemma value_mulFrom (xs ys acc : List Bool) :
    value (mulFrom xs ys acc)=2^xs.length*value acc+value xs.reverse*value ys := by
  induction xs generalizing acc with
  | nil => simp [mulFrom,value]
  | cons b xs ih =>
    simp only [mulFrom,ih,List.length_cons,pow_succ,List.reverse_cons,value_append,List.length_reverse]
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,value_add,value,Bool.toNat_false,
      Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
    all_goals ring

lemma normalize_mulFrom (xs ys : List Bool) :
    normalize (mulFrom xs.reverse ys [])=(value xs*value ys).bits := by
  rw [normalize_eq_bits,value_mulFrom,List.reverse_reverse,value,Nat.mul_zero,Nat.zero_add]

namespace Multiplication

def mStacks (a b c d e : List Bool) : Stacks (Fin 5) := ![a,b,c,d,e]
@[simp] lemma mStacks_0 (a b c d e : List Bool) : mStacks a b c d e 0=a := rfl
@[simp] lemma mStacks_1 (a b c d e : List Bool) : mStacks a b c d e 1=b := rfl
@[simp] lemma mStacks_2 (a b c d e : List Bool) : mStacks a b c d e 2=c := rfl
@[simp] lemma mStacks_3 (a b c d e : List Bool) : mStacks a b c d e 3=d := rfl
@[simp] lemma mStacks_4 (a b c d e : List Bool) : mStacks a b c d e 4=e := rfl

lemma upd0 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 0 t=mStacks t b c d e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd1 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 1 t=mStacks a t c d e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd2 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 2 t=mStacks a b t d e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd3 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 3 t=mStacks a b c t e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd4 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 4 t=mStacks a b c d t := by
  funext i; fin_cases i <;> simp [mStacks]

abbrev program : Program where
  K := Fin 5
  input := 0
  output := 3
  Label := Fin 6
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
          (.push 3 (fun _ => false)
            (.branch (fun s => s.2.1.getD false)
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 2)))
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 1)))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 5))))
    else if l=2 then
      .pop 0 (fun s b => (s.1,b,none))
        (.pop 3 (fun s b => (s.1,s.2.1,b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.branch (fun s => s.2.1.isSome)
              (.push 2 (fun s => s.2.1.getD false)
                (.push 4 (fun s => sumBit s.1 (s.2.1.getD false) (s.2.2.getD false))
                  (.load (fun s => (carryBit s.1 (s.2.1.getD false) (s.2.2.getD false),none,none))
                    (.goto (fun _ => 2)))))
              (.push 4 (fun s => sumBit s.1 false (s.2.2.getD false))
                (.load (fun s => (carryBit s.1 false (s.2.2.getD false),none,none))
                  (.goto (fun _ => 2)))))
            (.branch Prod.fst
              (.push 4 (fun _ => true)
                (.load (fun _ => (false,none,none)) (.goto (fun _ => 3))))
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 3))))))
    else if l=3 then
      .pop 2 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.push 0 (fun s => s.2.1.getD false)
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 3))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 4))))
    else if l=4 then
      .pop 4 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.push 3 (fun s => s.2.1.getD false)
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 4))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 1))))
    else
      .pop 0 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 5)))
          (.load (fun _ => (false,none,none)) .halt))

def cfg (l : Fin 6) (c : Bool) (a b d e f : List Bool) : program.machine.Cfg :=
  ⟨some l,(c,none,none),mStacks a b d e f⟩
def done (ys : List Bool) : program.machine.Cfg :=
  ⟨none,(false,none,none),mStacks [] [] [] ys []⟩

lemma initial (xs : List Bool) : initList program.machine xs=cfg 0 false xs [] [] [] [] := by
  rw [initList_bool]; congr 1
  funext i; fin_cases i <;> simp [program,mStacks]
lemma final (xs : List Bool) : haltList program.machine xs=done xs := by
  rw [haltList_bool]; congr 1
  funext i; fin_cases i <;> simp [program,mStacks]

lemma parse_nil (bs : List Bool) :
    program.machine.step (cfg 0 false [] bs [] [] [])=some (cfg 1 false [] bs [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (bs : List Bool) :
    program.machine.step (cfg 0 false [true] bs [] [] [])=some (cfg 1 false [] bs [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (as bs : List Bool) :
    program.machine.step (cfg 0 false (false::as) bs [] [] [])=some (cfg 1 false as bs [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (as bs : List Bool) :
    program.machine.step (cfg 0 false (true::b::as) bs [] [] [])=some (cfg 0 false as (b::bs) [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd1]; rfl

lemma process_nil (ys acc : List Bool) :
    program.machine.step (cfg 1 false ys [] [] acc [])=some (cfg 5 false ys [] [] acc []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd1]; rfl
lemma process_false (xs ys acc : List Bool) :
    program.machine.step (cfg 1 false ys (false::xs) [] acc [])=some (cfg 1 false ys xs [] (false::acc) []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd1,upd3]; rfl
lemma process_true (xs ys acc : List Bool) :
    program.machine.step (cfg 1 false ys (true::xs) [] acc [])=some (cfg 2 false ys xs [] (false::acc) []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd1,upd3]; rfl

lemma sum_nil (c : Bool) (bs ds fs : List Bool) :
    program.machine.step (cfg 2 c [] bs ds [] fs)=
      some (cfg 3 false [] bs ds [] ((if c then [true] else [])++fs)) := by
  cases c <;> simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd4]
  all_goals rfl
lemma sum_left (c x : Bool) (as bs ds fs : List Bool) :
    program.machine.step (cfg 2 c (x::as) bs ds [] fs)=
      some (cfg 2 (carryBit c x false) as bs (x::ds) [] (sumBit c x false::fs)) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd2,upd4]; rfl
lemma sum_right (c y : Bool) (bs ds es fs : List Bool) :
    program.machine.step (cfg 2 c [] bs ds (y::es) fs)=
      some (cfg 2 (carryBit c false y) [] bs ds es (sumBit c false y::fs)) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd4]; rfl
lemma sum_both (c x y : Bool) (as bs ds es fs : List Bool) :
    program.machine.step (cfg 2 c (x::as) bs ds (y::es) fs)=
      some (cfg 2 (carryBit c x y) as bs (x::ds) es (sumBit c x y::fs)) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd2,upd4]; rfl

lemma resty_nil (a b e : List Bool) :
    program.machine.step (cfg 3 false a b [] [] e)=some (cfg 4 false a b [] [] e) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd2]; rfl
lemma resty_cons (t : Bool) (a b c e : List Bool) :
    program.machine.step (cfg 3 false a b (t::c) [] e)=some (cfg 3 false (t::a) b c [] e) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd2,upd0]; rfl
lemma resta_nil (a b d : List Bool) :
    program.machine.step (cfg 4 false a b [] d [])=some (cfg 1 false a b [] d []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd4]; rfl
lemma resta_cons (t : Bool) (a b d e : List Bool) :
    program.machine.step (cfg 4 false a b [] d (t::e))=some (cfg 4 false a b [] (t::d) e) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd4,upd3]; rfl
lemma clear_nil (acc : List Bool) :
    program.machine.step (cfg 5 false [] [] [] acc [])=some (done acc) := by
  simp [FinTM2.step,cfg,done,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_cons (t : Bool) (ys acc : List Bool) :
    program.machine.step (cfg 5 false (t::ys) [] [] acc [])=some (cfg 5 false ys [] [] acc []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl

noncomputable def sum_outputs (c : Bool) (as bs ds es fs : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 c as bs ds es fs)
      (some (cfg 3 false [] bs (as.reverse++ds) [] ((add c as es).reverse++fs)))
      (as.length+es.length+1) := by
  induction as generalizing c es ds fs with
  | nil =>
    induction es generalizing c fs with
    | nil =>
      cases c with
      | false => simpa [add] using one_step (sum_nil false bs ds fs)
      | true => simpa [add] using one_step (sum_nil true bs ds fs)
    | cons y es ih =>
      have hh := step_then (sum_right c y bs ds es fs) (ih (carryBit c false y) (sumBit c false y::fs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,List.length_nil,Nat.zero_add]
        using hh
  | cons x as ih =>
    cases es with
    | nil =>
      have hh := step_then (sum_left c x as bs ds fs) (ih (carryBit c x false) (x::ds) [] (sumBit c x false::fs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,List.length_nil,Nat.add_zero]
        using hh
    | cons y es =>
      have hh := step_then (sum_both c x y as bs ds es fs)
        (ih (carryBit c x y) (x::ds) es (sumBit c x y::fs))
      simp only [add,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp; omega)

noncomputable def resta_outputs (a b d e : List Bool) :
    EvalsToInTime program.machine.step (cfg 4 false a b [] d e)
      (some (cfg 1 false a b [] (e.reverse++d) [])) (e.length+1) := by
  induction e generalizing d with
  | nil => exact one_step (resta_nil a b d)
  | cons t e ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using
      step_then (resta_cons t a b d e) (ih (t::d))

noncomputable def resty_outputs (a b c e : List Bool) :
    EvalsToInTime program.machine.step (cfg 3 false a b c [] e)
      (some (cfg 1 false (c.reverse++a) b [] e.reverse [])) (c.length+e.length+2) := by
  induction c generalizing a with
  | nil =>
    simpa only [List.reverse_nil,List.nil_append,List.length_nil,List.append_nil,Nat.zero_add,Nat.add_assoc] using
      step_then (resty_nil a b e) (resta_outputs a b [] e)
  | cons t c ih =>
    have hh := step_then (resty_cons t a b c e) (ih (t::a))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_right_comm] using hh

noncomputable def add_cycle (xs ys acc : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 false ys xs [] acc [])
      (some (cfg 1 false ys xs [] (add false ys acc) []))
      (2*ys.length+acc.length+(add false ys acc).length+3) := by
  have h1 := sum_outputs false ys xs [] acc []
  have h2 := resty_outputs [] xs ys.reverse (add false ys acc).reverse
  simp only [List.append_nil] at h1
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h2
  have hh := MetricKMedianRecovery.BitMachine.eval_trans h1 h2
  exact time_mono hh (by omega)

noncomputable def clear_outputs (ys acc : List Bool) :
    EvalsToInTime program.machine.step (cfg 5 false ys [] [] acc []) (some (done acc)) (ys.length+1) := by
  induction ys with
  | nil => exact one_step (clear_nil acc)
  | cons t ys ih => exact step_then (clear_cons t ys acc) ih

end Multiplication
end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
