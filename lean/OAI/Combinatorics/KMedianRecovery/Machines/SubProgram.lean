import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BorrowBit

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

abbrev subProgram : Program where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 4
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
    else if l=2 then
      .pop 2 (fun s b => (s.1,b,none))
        (.pop 0 (fun s b => (s.1,s.2.1,b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.push 1 (fun s => sumBit s.1 (s.2.1.getD false) (s.2.2.getD false))
              (.load (fun s => (borrowBit s.1 (s.2.1.getD false) (s.2.2.getD false),none,none))
                (.goto (fun _ => 2))))
            (.branch Prod.fst
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 3)))
              (.load (fun _ => (false,none,none)) .halt))))
    else
      .pop 1 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 3)))
          (.load (fun _ => (false,none,none)) .halt))

def cfg (l : Fin 4) (c : Bool) (x y z : List Bool) : subProgram.machine.Cfg :=
  ⟨some l,(c,none,none),triStacks x y z⟩
def done (ys : List Bool) : subProgram.machine.Cfg :=
  ⟨none,(false,none,none),triStacks [] ys []⟩

lemma sub_initial (xs : List Bool) : initList subProgram.machine xs=cfg 0 false xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [subProgram,triStacks]

lemma sub_final (xs : List Bool) : haltList subProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [subProgram,triStacks]

lemma parse_nil (ys : List Bool) :
    subProgram.machine.step (cfg 0 false [] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_one (ys : List Bool) :
    subProgram.machine.step (cfg 0 false [true] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_false (xs ys : List Bool) :
    subProgram.machine.step (cfg 0 false (false::xs) ys [])=some (cfg 1 false xs ys []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    subProgram.machine.step (cfg 0 false (true::b::xs) ys [])=some (cfg 0 false xs (b::ys) []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_one]
  rfl

lemma rev_nil (xs zs : List Bool) :
    subProgram.machine.step (cfg 1 false xs [] zs)=some (cfg 2 false xs [] zs) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl
lemma rev_cons (b : Bool) (xs ys zs : List Bool) :
    subProgram.machine.step (cfg 1 false xs (b::ys) zs)=some (cfg 1 false xs ys (b::zs)) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one,update_two]
  rfl

lemma clear_nil : subProgram.machine.step (cfg 3 false [] [] [])=some (done []) := by
  simp [FinTM2.step,cfg,done,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl
lemma clear_cons (b : Bool) (xs : List Bool) :
    subProgram.machine.step (cfg 3 false [] (b::xs) [])=some (cfg 3 false [] xs []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl

noncomputable def clear_outputs (xs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 3 false [] xs []) (some (done [])) (xs.length+1) := by
  induction xs with
  | nil => exact one_step clear_nil
  | cons b xs ih => simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (step_then (clear_cons b xs) ih)

lemma sum_nil_false (zs : List Bool) :
    subProgram.machine.step (cfg 2 false [] zs [])=some (done zs) := by
  simp [FinTM2.step,cfg,done,subProgram,TM2.step,TM2.stepAux,update_zero,update_two]
  rfl
lemma sum_nil_true (zs : List Bool) :
    subProgram.machine.step (cfg 2 true [] zs [])=some (cfg 3 false [] zs []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two]
  rfl
lemma sum_cons_nil (c x : Bool) (xs zs : List Bool) :
    subProgram.machine.step (cfg 2 c [] zs (x::xs))=
      some (cfg 2 (borrowBit c x false) [] (sumBit c x false::zs) xs) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_nil_cons (c y : Bool) (ys zs : List Bool) :
    subProgram.machine.step (cfg 2 c (y::ys) zs [])=
      some (cfg 2 (borrowBit c false y) ys (sumBit c false y::zs) []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_cons_cons (c x y : Bool) (xs ys zs : List Bool) :
    subProgram.machine.step (cfg 2 c (y::ys) zs (x::xs))=
      some (cfg 2 (borrowBit c x y) ys (sumBit c x y::zs) xs) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl

noncomputable def sum_outputs (c : Bool) (xs ys zs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 2 c ys zs xs)
      (some (done (if (difference c xs ys).2 then [] else (difference c xs ys).1.reverse++zs)))
        (2*(xs.length+ys.length)+zs.length+2) := by
  induction xs generalizing c ys zs with
  | nil =>
    induction ys generalizing c zs with
    | nil =>
      cases c with
      | false => simpa only [difference,Bool.false_eq_true,ite_false,List.reverse_nil,List.nil_append,
          List.length_nil,Nat.add_zero,Nat.mul_zero,Nat.zero_add] using
          time_mono (one_step (sum_nil_false zs)) (by omega : 1≤zs.length+2)
      | true => simpa only [difference,ite_true,List.length_nil,Nat.add_zero,Nat.mul_zero,Nat.zero_add,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          step_then (sum_nil_true zs) (clear_outputs zs)
    | cons y ys ih =>
      have hh := step_then (sum_nil_cons c y ys zs) (ih (borrowBit c false y) (sumBit c false y::zs))
      simp only [difference,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hh := step_then (sum_cons_nil c x xs zs) (ih (borrowBit c x false) [] (sumBit c x false::zs))
      simp only [difference,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)
    | cons y ys =>
      have hh := step_then (sum_cons_cons c x y xs ys zs) (ih (borrowBit c x y) ys (sumBit c x y::zs))
      simp only [difference,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def rev_outputs (xs ys zs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 1 false xs ys zs)
      (some (done ((subtract (ys.reverse++zs) xs).reverse)))
        (3*ys.length+2*zs.length+2*xs.length+3) := by
  induction ys generalizing zs with
  | nil =>
    have hh := step_then (rev_nil xs zs) (sum_outputs false zs xs [])
    simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.zero_add]
    dsimp only [subtract]
    split_ifs with hc
    · simpa only [hc,ite_true,List.reverse_nil] using time_mono hh (by simp only [List.length_nil]; omega)
    · simpa only [hc,Bool.false_eq_true,ite_false,List.append_nil] using time_mono hh (by simp only [List.length_nil]; omega)
  | cons b ys ih =>
    have hh := step_then (rev_cons b xs ys zs) (ih (b::zs))
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
    exact time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def parse_outputs (xs ys : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 0 false xs ys [])
      (some (done ((subtract ((extractPrefix xs).reverse++ys).reverse (discardPrefix xs)).reverse)))
        (4*xs.length+3*ys.length+4) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil =>
    have hh := step_then (parse_nil ys) (rev_outputs [] ys [])
    simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,
      List.length_nil,Nat.add_zero,Nat.zero_add] using time_mono hh (by simp)
  | singleton b =>
    cases b with
    | false =>
      have hh := step_then (parse_false [] ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp)
    | true =>
      have hh := step_then (parse_one ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      have hh := step_then (parse_false (c::xs) ys) (rev_outputs (c::xs) ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil] using
        time_mono hh (by simp only [List.length_nil,List.length_cons]; omega)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def subtractReverse_computes : PolyComputes (fun xs =>
    (subtract (extractPrefix xs) (discardPrefix xs)).reverse) where
  program := subProgram
  time := 4*Polynomial.X+4
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,sub_initial,sub_final,List.append_nil,
      List.reverse_reverse,List.length_nil,Nat.mul_zero,Nat.add_zero,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using parse_outputs xs []

noncomputable def subtract_computes : PolyComputes (fun xs =>
    normalize (subtract (extractPrefix xs) (discardPrefix xs))) :=
  (subtractReverse_computes.comp trim_computes).comp reverse_computes

noncomputable def subtraction : Turing.TM2ComputableInPolyTime
    (fun p : ℕ×ℕ => pairBits (p.1.bits,p.2.bits)) Nat.bits (fun p => p.1-p.2) :=
  subtract_computes.reencode _ _ (fun p => by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,normalize_subtract])

end BinarySubtraction
end MetricKMedianRecovery.BitMachine

end OAI
