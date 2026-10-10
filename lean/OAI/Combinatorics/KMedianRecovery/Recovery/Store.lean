import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EvalTrans

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace ProductBits

def store (a b c : List Bool) : Stacks (Fin 3) := ![a,b,c]
@[simp] lemma store0 (a b c : List Bool) : store a b c 0=a := rfl
@[simp] lemma store1 (a b c : List Bool) : store a b c 1=b := rfl
@[simp] lemma store2 (a b c : List Bool) : store a b c 2=c := rfl
lemma upd0 (a b c t : List Bool) : Function.update (store a b c) 0 t=store t b c := by
  funext i; fin_cases i <;> simp [store]
lemma upd1 (a b c t : List Bool) : Function.update (store a b c) 1 t=store a t c := by
  funext i; fin_cases i <;> simp [store]
lemma upd2 (a b c t : List Bool) : Function.update (store a b c) 2 t=store a b t := by
  funext i; fin_cases i <;> simp [store]

abbrev program (duplicate : Bool) : Program where
  K := Fin 3
  input := 0
  output := 0
  Label := Fin 4
  main := 0
  State := Option Bool
  initial := none
  code l := if l=0 then
    if duplicate then
      .pop 0 (fun _ b => b)
        (.branch Option.isSome
          (.push 1 (fun s => s.getD false)
            (.push 2 (fun s => s.getD false)
              (.load (fun _=>none) (.goto (fun _=>0)))))
          (.load (fun _=>none) (.goto (fun _=>2))))
    else
      .pop 0 (fun _ b => b)
        (.branch (fun s => decide (s=some true))
          (.pop 0 (fun _ b => b)
            (.branch Option.isSome
              (.push 1 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>0))))
              (.load (fun _=>none) (.goto (fun _=>1)))))
          (.load (fun _=>none) (.goto (fun _=>1))))
    else if l=1 then
      .pop 0 (fun _ b => b)
        (.branch Option.isSome
          (.push 2 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>1))))
          (.load (fun _=>none) (.goto (fun _=>2))))
    else if l=2 then
      .pop 1 (fun _ b => b)
        (.branch Option.isSome
          (.push 0 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>2))))
          (.push 0 (fun _=>false) (.load (fun _=>none) (.goto (fun _=>3)))))
    else
      .pop 2 (fun _ b => b)
        (.branch Option.isSome
          (.push 0 (fun s=>s.getD false)
            (.push 0 (fun _=>true) (.load (fun _=>none) (.goto (fun _=>3)))))
          (.load (fun _=>none) .halt))

def cfg (mode : Bool) (l : Fin 4) (a b c : List Bool) : (program mode).machine.Cfg :=
  ⟨some l,none,store a b c⟩
def done (mode : Bool) (out : List Bool) : (program mode).machine.Cfg :=
  ⟨none,none,store out [] []⟩
lemma copy_nil (b c : List Bool) :
    (program true).machine.step (cfg true 0 [] b c)=some (cfg true 2 [] b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma copy_cons (x : Bool) (a b c : List Bool) :
    (program true).machine.step (cfg true 0 (x::a) b c)=some (cfg true 0 a (x::b) (x::c)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1,upd2]; rfl
lemma parse_nil (b : List Bool) :
    (program false).machine.step (cfg false 0 [] b [])=some (cfg false 1 [] b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_false (a b : List Bool) :
    (program false).machine.step (cfg false 0 (false::a) b [])=some (cfg false 1 a b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_one (b : List Bool) :
    (program false).machine.step (cfg false 0 [true] b [])=some (cfg false 1 [] b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_true (x : Bool) (a b : List Bool) :
    (program false).machine.step (cfg false 0 (true::x::a) b [])=some (cfg false 0 a (x::b) []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl
lemma reverse_nil (mode : Bool) (b c : List Bool) :
    (program mode).machine.step (cfg mode 1 [] b c)=some (cfg mode 2 [] b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma reverse_cons (mode x : Bool) (a b c : List Bool) :
    (program mode).machine.step (cfg mode 1 (x::a) b c)=some (cfg mode 1 a b (x::c)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd2]; rfl
lemma restore_nil (mode : Bool) (a c : List Bool) :
    (program mode).machine.step (cfg mode 2 a [] c)=some (cfg mode 3 (false::a) [] c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1,upd0]; rfl
lemma restore_cons (mode x : Bool) (a b c : List Bool) :
    (program mode).machine.step (cfg mode 2 a (x::b) c)=some (cfg mode 2 (x::a) b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1,upd0]; rfl
lemma encode_nil (mode : Bool) (a : List Bool) :
    (program mode).machine.step (cfg mode 3 a [] [])=some (done mode a) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd2]; rfl
lemma encode_cons (mode x : Bool) (a c : List Bool) :
    (program mode).machine.step (cfg mode 3 a [] (x::c))=some (cfg mode 3 (true::x::a) [] c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd2,upd0]; rfl

noncomputable def copy_phase (a b c : List Bool) :
    EvalsToInTime (program true).machine.step (cfg true 0 a b c)
      (some (cfg true 2 [] (a.reverse++b) (a.reverse++c))) (a.length+1) := by
  induction a generalizing b c with
  | nil => exact one_step (copy_nil b c)
  | cons x a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (copy_cons x a b c) (ih (x::b) (x::c))

noncomputable def parse_phase (a b : List Bool) :
    EvalsToInTime (program false).machine.step (cfg false 0 a b [])
      (some (cfg false 1 (discardPrefix a) ((extractPrefix a).reverse++b) [])) (a.length+1) := by
  induction a using List.twoStepInduction generalizing b with
  | nil => exact one_step (parse_nil b)
  | singleton x =>
    cases x with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false [] b)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one b)) (by decide : 1≤2)
  | cons_cons x y a ih _ =>
    cases x with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (y::a) b)) (by simp : 1≤(false::y::a).length+1)
    | true =>
      have hh := step_then (parse_true y a b) (ih (y::b))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def reverse_phase (mode : Bool) (a b c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 1 a b c)
      (some (cfg mode 2 [] b (a.reverse++c))) (a.length+1) := by
  induction a generalizing c with
  | nil => exact one_step (reverse_nil mode b c)
  | cons x a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (reverse_cons mode x a b c) (ih (x::c))

noncomputable def restore_phase (mode : Bool) (a b c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 2 a b c)
      (some (cfg mode 3 (false::(b.reverse++a)) [] c)) (b.length+1) := by
  induction b generalizing a with
  | nil => exact one_step (restore_nil mode a c)
  | cons x b ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (restore_cons mode x a b c) (ih (x::a))

noncomputable def encode_phase (mode : Bool) (a c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 3 a [] c)
      (some (done mode (c.reverse.flatMap (fun b=>[true,b])++a))) (c.length+1) := by
  induction c generalizing a with
  | nil => exact one_step (encode_nil mode a)
  | cons x c ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      step_then (encode_cons mode x a c) (ih (true::x::a))

lemma initial (mode : Bool) (xs : List Bool) : initList (program mode).machine xs=cfg mode 0 xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]
lemma final (mode : Bool) (xs : List Bool) : haltList (program mode).machine xs=done mode xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]

noncomputable def duplicate_computes : PolyComputes (fun xs => pairBits (xs,xs)) where
  program := program true
  time := 3*Polynomial.X+3
  outputs xs := by
    have h1 := copy_phase xs [] []
    have h2 := restore_phase true [] xs.reverse xs.reverse
    have h3 := encode_phase true (false::xs) xs.reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3
    have hh := eval_trans h1 (eval_trans h2 h3)
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,pairBits,List.append_assoc,List.cons_append,List.nil_append]
    exact time_mono hh (by omega)

lemma projections_length (xs : List Bool) :
    (extractPrefix xs).length≤xs.length ∧ (discardPrefix xs).length≤xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [extractPrefix,discardPrefix]
  | singleton b => cases b <;> simp [extractPrefix,discardPrefix]
  | cons_cons b c xs ih _ => cases b <;> simp only [extractPrefix,discardPrefix,List.length_cons,List.length_nil] <;> omega

noncomputable def swap_computes : PolyComputes (fun xs => pairBits (discardPrefix xs,extractPrefix xs)) where
  program := program false
  time := 4*Polynomial.X+4
  outputs xs := by
    let a := extractPrefix xs
    let b := discardPrefix xs
    have h1 := parse_phase xs []
    have h2 := reverse_phase false b a.reverse []
    have h3 := restore_phase false [] a.reverse b.reverse
    have h4 := encode_phase false (false::a) b.reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3 h4
    have hh := eval_trans h1 (eval_trans h2 (eval_trans h3 h4))
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,pairBits,List.append_assoc,List.cons_append,List.nil_append]
    apply time_mono hh
    have hp := projections_length xs
    change a.length≤xs.length ∧ b.length≤xs.length at hp
    omega

end ProductBits

noncomputable def PolyComputes.pair {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun xs=>pairBits (f xs,g xs)) := by
  have h := (((ProductBits.duplicate_computes.comp hf.mapLeft).comp ProductBits.swap_computes).comp
    hg.mapLeft).comp ProductBits.swap_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using h

end MetricKMedianRecovery.BitMachine

end OAI
