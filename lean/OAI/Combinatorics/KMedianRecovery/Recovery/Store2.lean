import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EvalTrans
import OAI.Combinatorics.KMedianRecovery.Recovery.Store
import OAI.Combinatorics.KMedianRecovery.Encoding.PushWord

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

def store (xs ys : List Bool) : Stacks (Fin 2) := ![xs,ys]
@[simp] lemma store0 (xs ys : List Bool) : store xs ys 0=xs := rfl
@[simp] lemma store1 (xs ys : List Bool) : store xs ys 1=ys := rfl
lemma upd0 (xs ys zs : List Bool) : Function.update (store xs ys) 0 zs=store zs ys := by
  funext i; fin_cases i <;> simp [store]
lemma upd1 (xs ys zs : List Bool) : Function.update (store xs ys) 1 zs=store xs zs := by
  funext i; fin_cases i <;> simp [store]

abbrev appendProgram : Program where
  K := Fin 2
  input := 0
  output := 0
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  code l := if l then
    .pop 1 (fun _ b=>b)
      (.branch Option.isSome
        (.push 0 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>true))))
        (.load (fun _=>none) .halt))
    else
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.push 1 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>false))))
              (.load (fun _=>none) (.goto (fun _=>true)))))
          (.load (fun _=>none) (.goto (fun _=>true))))

def cfg (l : Bool) (xs ys : List Bool) : appendProgram.machine.Cfg := ⟨some l,none,store xs ys⟩
def done (xs : List Bool) : appendProgram.machine.Cfg := ⟨none,none,store xs []⟩

lemma parse_nil (ys : List Bool) : appendProgram.machine.step (cfg false [] ys)=some (cfg true [] ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (ys : List Bool) : appendProgram.machine.step (cfg false [true] ys)=some (cfg true [] ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (xs ys : List Bool) : appendProgram.machine.step (cfg false (false::xs) ys)=some (cfg true xs ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    appendProgram.machine.step (cfg false (true::b::xs) ys)=some (cfg false xs (b::ys)) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma restore_nil (xs : List Bool) : appendProgram.machine.step (cfg true xs [])=some (done xs) := by
  simp [FinTM2.step,appendProgram,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) :
    appendProgram.machine.step (cfg true xs (b::ys))=some (cfg true (b::xs) ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime appendProgram.machine.step (cfg false xs ys)
      (some (cfg true (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact one_step (parse_nil ys)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_false [] ys)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_one ys)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) ys)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (xs ys : List Bool) :
    EvalsToInTime appendProgram.machine.step (cfg true xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

lemma initial (xs : List Bool) : initList appendProgram.machine xs=cfg false xs [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [appendProgram,store]
lemma final (xs : List Bool) : haltList appendProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [appendProgram,store]

noncomputable def append_computes : PolyComputes (fun xs=>extractPrefix xs++discardPrefix xs) where
  program := appendProgram
  time := 2*Polynomial.X+2
  outputs xs := by
    have h1 := parse_phase xs []
    have h2 := restore_phase (discardPrefix xs) (extractPrefix xs).reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2
    have hh := eval_trans h1 h2
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    have hl := extractPrefix_length xs
    exact time_mono hh (by omega)

abbrev prefixProgram (b : Bool) : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .push () (fun _=>b) .halt

noncomputable def prefix_computes (b : Bool) : PolyComputes (List.cons b) where
  program := prefixProgram b
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    simp [initList_bool,haltList_bool,FinTM2.step,prefixProgram,TM2.step,TM2.stepAux,unit_update]
    rfl

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .pop () (fun _ _=>()) .halt

noncomputable def tail_computes : PolyComputes (List.tail : List Bool → List Bool) where
  program := tailProgram
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    cases xs <;> simp [initList_bool,haltList_bool,FinTM2.step,tailProgram,TM2.step,TM2.stepAux,unit_update]
    all_goals rfl

end WordOperations

noncomputable def PolyComputes.append {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun xs=>f xs++g xs) := by
  have hh := (hf.pair hg).comp WordOperations.append_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def const_computes (ys : List Bool) : PolyComputes (fun _=>ys) := by
  have hh := FiniteFold.computes () (fun _ _=>()) (fun _=>ys)
  exact hh

end MetricKMedianRecovery.BitMachine

end OAI
