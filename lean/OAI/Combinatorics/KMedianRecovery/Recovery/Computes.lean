import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Store
import OAI.Combinatorics.KMedianRecovery.Machines.SubProgram
import OAI.Combinatorics.KMedianRecovery.Recovery.Store2

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open Turing
namespace BinarySubtraction
open BinaryArithmetic

lemma bits_eq_nil (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hh := value_bits n
    rw [h] at hh
    exact hh.symm
  · rintro rfl
    rfl

noncomputable def le_computes : PolyComputes (fun xs=>
    [decide (value (extractPrefix xs)≤value (discardPrefix xs))]) := by
  have hh := subtract_computes.comp isEmpty_computes
  simpa only [Function.comp_def,normalize_eq_bits,value_subtract,bits_eq_nil,
    Nat.sub_eq_zero_iff_le] using hh

noncomputable def lessEqual : TM2ComputableInPolyTime
    (fun p : ℕ×ℕ=>pairBits (p.1.bits,p.2.bits)) (fun b:Bool=>[b]) (fun p=>decide (p.1≤p.2)) :=
  le_computes.reencode _ _ (fun p=>by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,value_bits])

end BinarySubtraction
end
open Turing Turing.TM2 StateTransition
namespace WordSelection
open WordOperations

def choose (xs : List Bool) : List Bool :=
  if xs.head?=some true then extractPrefix xs.tail else discardPrefix xs.tail

abbrev program : Program where
  K := Fin 2
  input := 0
  output := 0
  Label := Fin 5
  main := 0
  State := Option Bool
  initial := none
  code l := if l=0 then
    .pop 0 (fun _ b=>b)
      (.branch (fun s=>decide (s=some true))
        (.load (fun _=>none) (.goto (fun _=>1)))
        (.load (fun _=>none) (.goto (fun _=>2))))
    else if l=1 then
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.push 1 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>1))))
              (.load (fun _=>none) (.goto (fun _=>3)))))
          (.load (fun _=>none) (.goto (fun _=>3))))
    else if l=2 then
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.load (fun _=>none) (.goto (fun _=>2)))
              (.load (fun _=>none) .halt)))
          (.load (fun _=>none) .halt))
    else if l=3 then
      .pop 0 (fun _ b=>b)
        (.branch Option.isSome
          (.load (fun _=>none) (.goto (fun _=>3)))
          (.load (fun _=>none) (.goto (fun _=>4))))
    else
      .pop 1 (fun _ b=>b)
        (.branch Option.isSome
          (.push 0 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>4))))
          (.load (fun _=>none) .halt))

def cfg (l : Fin 5) (xs ys : List Bool) : program.machine.Cfg := ⟨some l,none,store xs ys⟩
def done (xs : List Bool) : program.machine.Cfg := ⟨none,none,store xs []⟩

lemma start_true (xs : List Bool) : program.machine.step (cfg 0 (true::xs) [])=some (cfg 1 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma start_false (xs : List Bool) : program.machine.step (cfg 0 (false::xs) [])=some (cfg 2 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma start_nil : program.machine.step (cfg 0 [] [])=some (cfg 2 [] []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_nil (ys : List Bool) : program.machine.step (cfg 1 [] ys)=some (cfg 3 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (ys : List Bool) : program.machine.step (cfg 1 [true] ys)=some (cfg 3 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (xs ys : List Bool) : program.machine.step (cfg 1 (false::xs) ys)=some (cfg 3 xs ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    program.machine.step (cfg 1 (true::b::xs) ys)=some (cfg 1 xs (b::ys)) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma discard_nil : program.machine.step (cfg 2 [] [])=some (done []) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_one : program.machine.step (cfg 2 [true] [])=some (done []) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_false (xs : List Bool) : program.machine.step (cfg 2 (false::xs) [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_true (b : Bool) (xs : List Bool) :
    program.machine.step (cfg 2 (true::b::xs) [])=some (cfg 2 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_nil (ys : List Bool) : program.machine.step (cfg 3 [] ys)=some (cfg 4 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 3 (b::xs) ys)=some (cfg 3 xs ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma restore_nil (xs : List Bool) : program.machine.step (cfg 4 xs [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 4 xs (b::ys))=some (cfg 4 (b::xs) ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs ys)
      (some (cfg 3 (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
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
    EvalsToInTime program.machine.step (cfg 4 xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

noncomputable def discard_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 xs []) (some (done (discardPrefix xs))) (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step discard_nil
  | singleton b =>
    cases b with
    | false => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step (discard_false [])) (by decide : 1≤2)
    | true => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step discard_one) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [discardPrefix] using
        time_mono (one_step (discard_false (c::xs))) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (discard_true c xs) ih
      simp only [discardPrefix]
      exact time_mono hh (by simp)

noncomputable def clear_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 3 xs ys) (some (cfg 4 [] ys)) (xs.length+1) := by
  induction xs with
  | nil => exact one_step (clear_nil ys)
  | cons b xs ih => simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (step_then (clear_cons b xs ys) ih)

noncomputable def true_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs []) (some (done (extractPrefix xs))) (3*xs.length+3) := by
  have h1 := parse_phase xs []
  have h2 := clear_phase (discardPrefix xs) (extractPrefix xs).reverse
  have h3 := restore_phase [] (extractPrefix xs).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h3
  have hh := eval_trans h1 (eval_trans h2 h3)
  have hl := ProductBits.projections_length xs
  exact time_mono hh (by omega)

noncomputable def outputs (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 0 xs []) (some (done (choose xs))) (4*xs.length+4) := by
  cases xs with
  | nil =>
    have hh := step_then start_nil (one_step discard_nil)
    exact time_mono hh (by decide : 2≤4)
  | cons b xs =>
    cases b with
    | false =>
      have hh := step_then (start_false xs) (discard_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,Option.some.injEq,Bool.false_eq_true,ite_false] using
        time_mono hh (by simp only [List.length_cons]; omega)
    | true =>
      have hh := step_then (start_true xs) (true_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,ite_true] using
        time_mono hh (by simp only [List.length_cons]; omega)

lemma initial (xs : List Bool) : initList program.machine xs=cfg 0 xs [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]
lemma final (xs : List Bool) : haltList program.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]

noncomputable def choose_computes : PolyComputes choose where
  program := program
  time := 4*Polynomial.X+4
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using outputs xs

end WordSelection

noncomputable def PolyComputes.cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyComputes (fun xs=>[p xs])) (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun xs=>if p xs then f xs else g xs) := by
  have hh := (hp.append (hf.pair hg)).comp WordSelection.choose_computes
  simpa only [Function.comp_def,List.singleton_append,WordSelection.choose,List.head?_cons,
    List.tail_cons,Option.some.injEq,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def id_computes : PolyComputes id := by
  have he : (List.reverse ∘ List.reverse : List Bool → List Bool) = id := by
    funext x
    exact List.reverse_reverse x
  rw [← he]
  exact reverse_computes.comp reverse_computes

end MetricKMedianRecovery.BitMachine

end OAI
