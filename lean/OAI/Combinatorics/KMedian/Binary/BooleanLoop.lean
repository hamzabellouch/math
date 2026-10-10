import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanPolynomial

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Loop
variable (M : Machine)
abbrev Key := M.K ⊕ Unit
abbrev Label := M.Label ⊕ Option Bool
abbrev State := M.State × Option Bool
abbrev auxiliary : Key M := .inr ()
abbrev check : Label M := .inr none
abbrev phase (b : Bool) : Label M := .inr (some b)

def body : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j <;>
      simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (check M)
  stop := .goto (fun _ => check M)
  stop_spec _ _ := rfl

def source (b : Bool) : Key M := if b then auxiliary M else .inl M.output

def target (b : Bool) : Key M := if b then .inl M.input else auxiliary M

 theorem source_ne_target (b : Bool) : source M b ≠ target M b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M := if b then .inl M.main else phase M true

def clean (v : State M) : State M := (v.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M b) (fun v c => (v.1,c))
    (.branch (fun v => v.2.isSome)
      (.push (target M b) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => phase M b))))
      (.load (clean M) (.goto (fun _ => following M b))))

def checkCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v c => (v.1,c))
    (.branch (fun v => v.2.getD false)
      (.load (clean M) (.goto (fun _ => phase M false)))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M).stmt (M.code l)
  | .inr none => checkCode M
  | .inr (some b) => transfer M b

abbrev machine : Machine where
  K := Key M
  input := .inl M.input
  output := .inl M.output
  Label := Label M
  main := .inl M.main
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (l : M.Label) : (machine M).code ((body M).label l)=
    (body M).stmt (M.code l) := rfl

 theorem initial_body (s : List Bool) : (body M).cfg (M.initialCfg s)=
    (machine M).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,body,Machine.initialCfg]

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M).Cfg :=
  ⟨some (phase M b),(M.initial,none),twoStacks (source M b) (target M b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M).step (transferCfg M b (x::xs) ys)=some (transferCfg M b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) (x::xs) ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M b)),twoStacks_target (source_ne_target M b)]
  rw [twoStacks_move (source_ne_target M b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M).step xs.length (transferCfg M b xs ys)
      (transferCfg M b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M).step (transferCfg M b [] ys)=
      some ⟨some (following M b),(M.initial,none),twoStacks (source M b) (target M b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem transfer_change (ys : List Bool) :
    (machine M).step (transferCfg M false [] ys)=some (transferCfg M true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary]

 theorem transfer_end (ys : List Bool) :
    (machine M).step (transferCfg M true [] ys)=some ((machine M).initialCfg ys) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Machine.initialCfg,source,target,twoStacks,auxiliary]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M).step (2*xs.length+2) (transferCfg M false xs []) ((machine M).initialCfg xs) := by
  have h₁ := transfer_run M false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M xs.reverse) (transfer_run M true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

def checkCfg (xs : List Bool) : (machine M).Cfg :=
  ⟨some (check M),(M.initial,none),fun k => if k=Sum.inl M.output then xs else []⟩

 theorem body_final (xs : List Bool) : (body M).cfg (M.finalCfg xs)=checkCfg M xs := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [body,Embedding.cfg,Machine.finalCfg,checkCfg]

 theorem check_step (b : Bool) (xs : List Bool) :
    (machine M).step (checkCfg M (b::xs))=
      some ⟨if b then some (phase M false) else none,(M.initial,none),
        fun k => if k=Sum.inl M.output then xs else []⟩ := by
  change some (TM2.stepAux (checkCode M) (M.initial,none)
    (fun k => if k=Sum.inl M.output then b::xs else []))=_
  simp only [checkCode,TM2.stepAux,List.head?_cons,List.tail_cons,
    Option.getD_some,clean,ite_true]
  cases b <;> simp only [Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    apply congrArg some
    apply cfg_ext <;> try rfl
    funext k
    by_cases h : k=Sum.inl M.output <;> simp [h]

 theorem check_false (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (false::xs)))=some ((machine M).finalCfg xs) := by
  rw [body_final,check_step]
  rfl

 theorem check_true (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (true::xs)))=some (transferCfg M false xs []) := by
  rw [body_final,check_step]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,twoStacks,source,target,auxiliary]

 theorem stop {s t : List Bool} {n : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (false::t))) :
    Trace (machine M).step (n+1) ((machine M).initialCfg s) ((machine M).finalCfg t) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  exact h.trans (Trace.cons (check_false M t) (Trace.refl _))

 theorem next {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (true::t)))
    (hR : Trace (machine M).step m ((machine M).initialCfg t) ((machine M).finalCfg u)) :
    Trace (machine M).step (n+2*t.length+3+m) ((machine M).initialCfg s) ((machine M).finalCfg u) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  have hg := Trace.cons (check_true M t) (transfer_full M t)
  have hh := (h.trans hg).trans hR
  simpa only [Nat.add_assoc,show 2*t.length+2+1=2*t.length+3 by omega] using hh

end Loop

def encodeLoop {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : β ⊕ α → List Bool
  | .inl b => false::eb b
  | .inr a => true::ea a

inductive BoundedRun {α β : Type} (ea : α → List Bool) (f : α → β ⊕ α) (S : ℕ) :
    ℕ → α → β → Prop
  | stop {a b} : (ea a).length ≤ S → f a=.inl b → BoundedRun ea f S 1 a b
  | step {a a' b n} : (ea a).length ≤ S → f a=.inr a' →
      BoundedRun ea f S n a' b → BoundedRun ea f S (n+1) a b

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

noncomputable def passTime (P : PolyProgram ea (encodeLoop ea eb) f) (S : ℕ) : ℕ :=
  P.time.eval S+2*P.sizeBound.eval S+3

 theorem run_loop (P : PolyProgram ea (encodeLoop ea eb) f) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) :
    ∃ t ≤ n*P.passTime S, Trace (Loop.machine P.machine).step t
      ((Loop.machine P.machine).initialCfg (ea a)) ((Loop.machine P.machine).finalCfg (eb b)) := by
  induction h with
  | @stop a b ha hab =>
      have hp := P.outputs a
      have ht : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (false::eb b)) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [hab,encodeLoop] using hh
      refine ⟨hp.steps+1,?_,Loop.stop P.machine ht⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      simp only [passTime,one_mul]
      omega
  | @step a a' b n ha haa' h ih =>
      obtain ⟨t,ht,htrace⟩ := ih
      have hp := P.outputs a
      have hb : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (true::ea a')) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [haa',encodeLoop] using hh
      refine ⟨hp.steps+2*(ea a').length+3+t,?_,Loop.next P.machine hb htrace⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      have hl := (P.length_bound a).trans (polynomial_eval_mono P.sizeBound ha)
      simp only [haa',encodeLoop,List.length_cons] at hl
      dsimp only [passTime] at ht ⊢
      rw [Nat.add_mul]
      omega

noncomputable def loop (P : PolyProgram ea (encodeLoop ea eb) f) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun ea f (sizes.eval (ea a).length) n a (g a)) : PolyProgram ea eb g where
  machine := Loop.machine P.machine
  time := iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    refine ⟨⟨⟨t,htrace.iterate_eq⟩,?_⟩⟩
    refine ht.trans ?_
    simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp,
      Polynomial.eval_ofNat,passTime] using Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
