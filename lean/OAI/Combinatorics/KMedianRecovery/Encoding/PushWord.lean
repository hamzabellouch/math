import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StepThen

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def pushWord {K L S : Type} (k : K) : List Bool → TM2.Stmt (fun _ : K=>Bool) L S → TM2.Stmt (fun _ : K=>Bool) L S
  | [],c => c
  | b::bs,c => pushWord k bs (.push k (fun _=>b) c)

lemma pushWord_step {K L S : Type} [DecidableEq K] (k : K) (bs : List Bool)
    (c : TM2.Stmt (fun _ : K=>Bool) L S) (v : S) (s : Stacks K) :
    TM2.stepAux (pushWord k bs c) v s=TM2.stepAux c v (Function.update s k (bs++s k)) := by
  induction bs generalizing c with
  | nil => simp only [pushWord,List.nil_append,Function.update_eq_self]
  | cons b bs ih =>
    rw [pushWord,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

namespace FiniteFold
variable {Q : Type} [Fintype Q] (q₀ : Q) (next : Q → Bool → Q) (out : Q → List Bool)

abbrev program : Program where
  K := Unit
  input := ()
  output := ()
  Label := Option Q
  main := none
  State := Q × Option Bool
  initial := (q₀,none)
  code l := match l with
    | none => .pop () (fun q b=>(q.1,b))
      (.branch (fun q=>q.2.isSome)
        (.load (fun q=>(next q.1 (q.2.getD false),none)) (.goto (fun _=>none)))
        (.goto (fun q=>some q.1)))
    | some q => pushWord () (out q) (.load (fun _=>(q₀,none)) .halt)

def cfg (q : Q) (xs : List Bool) : (program q₀ next out).machine.Cfg :=
  ⟨some none,(q,none),fun _=>xs⟩
def finish (q : Q) : (program q₀ next out).machine.Cfg :=
  ⟨some (some q),(q,none),fun _=>[]⟩
def done (xs : List Bool) : (program q₀ next out).machine.Cfg :=
  ⟨none,(q₀,none),fun _=>xs⟩

lemma nil_step (q : Q) : (program q₀ next out).machine.step (cfg q₀ next out q [])=
    some (finish q₀ next out q) := by
  simp [FinTM2.step,program,cfg,finish,TM2.step,TM2.stepAux]
  rfl
lemma cons_step (q : Q) (b : Bool) (xs : List Bool) :
    (program q₀ next out).machine.step (cfg q₀ next out q (b::xs))=
      some (cfg q₀ next out (next q b) xs) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma finish_step (q : Q) : (program q₀ next out).machine.step (finish q₀ next out q)=
    some (done q₀ next out (out q)) := by
  simp [FinTM2.step,program,finish,done,TM2.step,pushWord_step,TM2.stepAux,unit_update]
  rfl

noncomputable def outputs (q : Q) (xs : List Bool) :
    EvalsToInTime (program q₀ next out).machine.step (cfg q₀ next out q xs)
      (some (done q₀ next out (out (xs.foldl next q)))) (xs.length+2) := by
  induction xs generalizing q with
  | nil => exact step_then (nil_step q₀ next out q) (one_step (finish_step q₀ next out q))
  | cons b xs ih =>
    simpa only [List.foldl_cons,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      step_then (cons_step q₀ next out q b xs) (ih (next q b))

lemma initial (xs : List Bool) : initList (program q₀ next out).machine xs=cfg q₀ next out q₀ xs := by
  rw [initList_bool]
  congr 1
lemma final (xs : List Bool) : haltList (program q₀ next out).machine xs=done q₀ next out xs := by
  rw [haltList_bool]
  congr 1

noncomputable def computes : PolyComputes (fun xs=>out (xs.foldl next q₀)) where
  program := program q₀ next out
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_ofNat] using outputs q₀ next out q₀ xs

end FiniteFold

lemma fold_orElse (xs : List Bool) (q : Option Bool) :
    xs.foldl (fun q b=>q.orElse (fun _=>some b)) q=q.orElse (fun _=>xs.head?) := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons,ih]
    cases q <;> simp

noncomputable def head_computes : PolyComputes (fun xs=>[xs.head?.getD false]) := by
  have hh := FiniteFold.computes (none : Option Bool) (fun q b=>q.orElse (fun _=>some b)) (fun q=>[q.getD false])
  simpa only [fold_orElse,Option.orElse_none] using hh

lemma fold_empty (xs : List Bool) (q : Bool) :
    xs.foldl (fun _ _=>false) q=if xs=[] then q else false := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih => simp [ih]

noncomputable def isEmpty_computes : PolyComputes (fun xs=>[decide (xs=[])]) := by
  have hh := FiniteFold.computes true (fun _ _=>false) (fun q=>[q])
  simpa [fold_empty] using hh

end MetricKMedianRecovery.BitMachine

end OAI
