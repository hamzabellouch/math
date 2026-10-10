import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanEmbedding

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Turing Function

namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.K M.Label M.State (Key M N) (Label M N) (State M N) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,N.initial,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl.injEq]
    · simp only [update_apply,Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.K N.Label N.State (Key M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  read v := v.2.1
  write v x := (v.1,x,v.2.2)
  state v := (M.initial,v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim (fun _ => []) (Sum.elim (fun _ => []) s)
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl_ne_inr,ite_false]
    · rcases j with j | j <;> simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inr.injEq,Sum.inl_ne_inr,ite_false]
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output

def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

 theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1,v.2.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1,v.2.1,c))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => v.2.2.getD false)
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  input := .inl M.input
  output := .inr (.inr N.output)
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial,N.initial,none)
  code := code M N

 theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l)=
    (left M N).stmt (M.code l) := rfl

 theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l)=
    (right M N).stmt (N.code l) := rfl

 theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s)=
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,left,Machine.initialCfg,machine]

 theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s)=
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.finalCfg,machine]
  · rcases k with k | k <;> simp [Embedding.cfg,right,Machine.finalCfg,machine]

end Compose

def twoStacks {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) (k : K) : List Bool :=
  if k=a then xs else if k=b then ys else []

@[simp] theorem twoStacks_source {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) :
    twoStacks a b xs ys a=xs := by simp [twoStacks]

@[simp] theorem twoStacks_target {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (xs ys : List Bool) : twoStacks a b xs ys b=ys := by simp [twoStacks,h.symm]

 theorem twoStacks_move {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (x : Bool) (xs ys : List Bool) :
    update (update (twoStacks a b (x::xs) ys) a xs) b (x::ys)=twoStacks a b xs (x::ys) := by
  funext k
  by_cases ha : k=a
  · subst k; simp [h,twoStacks]
  · by_cases hb : k=b
    · subst k; simp [h.symm,twoStacks]
    · simp [ha,hb,twoStacks]

 theorem twoStacks_pop_empty {K : Type} [DecidableEq K] (a b : K) (ys : List Bool) :
    update (twoStacks a b [] ys) a []=twoStacks a b [] ys := by
  funext k
  by_cases h : k=a <;> simp [twoStacks,h]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial,N.initial,none),
    twoStacks (source M N b) (target M N b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x::xs) ys)=
      some (transferCfg M N b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) (x::xs) ys))=some (transferCfg M N b xs (x::ys))
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M N b)),twoStacks_target (source_ne_target M N b)]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys)=
      some ⟨some (following M N b),(M.initial,N.initial,none),
        twoStacks (source M N b) (target M N b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem left_final_transfer (xs : List Bool) :
    (left M N).cfg (M.finalCfg xs)=transferCfg M N false xs [] := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_change (ys : List Bool) :
    (machine M N).step (transferCfg M N false [] ys)=some (transferCfg M N true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_end (ys : List Bool) :
    (machine M N).step (transferCfg M N true [] ys)=some ((right M N).cfg (N.initialCfg ys)) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M N).step (2*xs.length+2)
      ((left M N).cfg (M.finalCfg xs)) ((right M N).cfg (N.initialCfg xs)) := by
  rw [left_final_transfer]
  have h₁ := transfer_run M N false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M N xs.reverse) (transfer_run M N true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M N xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

 theorem run {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg t))
    (hN : Trace N.step m (N.initialCfg t) (N.finalCfg u)) :
    Trace (machine M N).step (n+2*t.length+2+m)
      ((machine M N).initialCfg s) ((machine M N).finalCfg u) := by
  have h₁ := (left M N).trace M.code (machine M N).code (code_left M N) hM
  have h₂ := (right M N).trace N.code (machine M N).code (code_right M N) hN
  rw [initial_left] at h₁
  rw [final_right] at h₂
  have hh := (h₁.trans (transfer_full M N t)).trans h₂
  simpa only [Machine.step,machine,Nat.add_assoc] using hh

end Compose
end MetricKMedian.Binary
end

end OAI
