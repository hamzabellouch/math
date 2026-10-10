import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.ExtractPrefix

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def frameStacks {K L : Type} (s : Stacks K) (t : Stacks L) : Stacks (K⊕L) := Sum.elim s t

@[simp] lemma frameStacks_inl {K L : Type} (s : Stacks K) (t : Stacks L) (k : K) :
    frameStacks s t (.inl k)=s k := rfl

@[simp] lemma frameStacks_inr {K L : Type} (s : Stacks K) (t : Stacks L) (k : L) :
    frameStacks s t (.inr k)=t k := rfl

lemma frameStacks_update {K L : Type} [DecidableEq K] [DecidableEq L]
    (s : Stacks K) (t : Stacks L) (k : K) (xs : List Bool) :
    frameStacks (Function.update s k xs) t = Function.update (frameStacks s t) (.inl k) xs := by
  funext i
  cases i <;> simp [frameStacks,Function.update_apply]

lemma stepAux_frame {K L A B S T : Type} [DecidableEq K] [DecidableEq L]
    (el : A → B) (es : S → T) (rs : T → S) (h : ∀ s,rs (es s)=s)
    (ret : Option B) (q : TM2.Stmt (fun _ : K => Bool) A S)
    (s : S) (stk : Stacks K) (extra : Stacks L) :
    TM2.stepAux (renameStmt (Function.Embedding.inl) el es rs ret q) (es s)
      (frameStacks stk extra) =
    ⟨(TM2.stepAux q s stk).l.elim ret (fun a => some (el a)),
      es (TM2.stepAux q s stk).var,frameStacks (TM2.stepAux q s stk).stk extra⟩ := by
  induction q generalizing s stk with
  | push k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl,
      ←frameStacks_update] using ih s (Function.update stk k (f s::stk k))
  | peek k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl] using
      ih (f s (stk k).head?) stk
  | pop k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl,
      ←frameStacks_update] using ih (f s (stk k).head?) (Function.update stk k (stk k).tail)
  | load f q ih => simpa only [renameStmt,TM2.stepAux,h] using ih (f s) stk
  | branch f q r ihq ihr =>
    simp only [renameStmt,TM2.stepAux,h]
    cases f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [renameStmt,TM2.stepAux,h,Option.elim_some]
  | halt => cases ret <;> rfl

lemma extractPrefix_length (bits : List Bool) : (extractPrefix bits).length≤bits.length := by
  induction bits using List.twoStepInduction with
  | nil => simp [extractPrefix]
  | singleton b => cases b <;> simp [extractPrefix]
  | cons_cons b c bits ih _ =>
    cases b <;> simp only [extractPrefix,List.length_cons,List.length_nil] <;> omega

namespace MapLeft
variable (p : Program)

abbrev Stack := p.K ⊕ Fin 2
abbrev Label := p.Label ⊕ Fin 4
abbrev State := p.State × Option Bool

def mapStacks (s : Stacks p.K) (a b : List Bool) : Stacks (Stack p) := frameStacks s ![a,b]
@[simp] lemma stacks_left (s : Stacks p.K) (a b : List Bool) (k : p.K) :
    mapStacks p s a b (.inl k)=s k := rfl
@[simp] lemma stacks_zero (s : Stacks p.K) (a b : List Bool) :
    mapStacks p s a b (.inr 0)=a := rfl
@[simp] lemma stacks_one (s : Stacks p.K) (a b : List Bool) :
    mapStacks p s a b (.inr 1)=b := rfl
lemma updLeft (s : Stacks p.K) (a b t : List Bool) (k : p.K) :
    Function.update (mapStacks p s a b) (.inl k) t=mapStacks p (Function.update s k t) a b :=
  (frameStacks_update _ _ _ _).symm
lemma upd0 (s : Stacks p.K) (a b t : List Bool) :
    Function.update (mapStacks p s a b) (.inr 0) t=mapStacks p s t b := by
  funext i
  cases i with
  | inl k => simp [mapStacks]
  | inr k => fin_cases k <;> simp [mapStacks]
lemma upd1 (s : Stacks p.K) (a b t : List Bool) :
    Function.update (mapStacks p s a b) (.inr 1) t=mapStacks p s a t := by
  funext i
  cases i with
  | inl k => simp [mapStacks]
  | inr k => fin_cases k <;> simp [mapStacks]

abbrev program : Program where
  K := Stack p
  input := .inr 1
  output := .inr 1
  Label := Label p
  main := .inr 0
  State := State p
  initial := (p.initial,none)
  code l := match l with
    | .inl i => renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none)) Prod.fst
        (some (.inr 2)) (p.code i)
    | .inr i => if i=0 then
        .pop (.inr 1) (fun s b => (s.1,b))
          (.branch (fun s => decide (s.2=some true))
            (.pop (.inr 1) (fun s b => (s.1,b))
              (.branch (fun s => s.2.isSome)
                (.push (.inr 0) (fun s => s.2.getD false)
                  (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 0))))
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1)))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
      else if i=1 then
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inl p.input) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inl p.main))))
      else if i=2 then
        .pop (.inl p.output) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 0) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 2))))
            (.push (.inr 1) (fun _ => false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3)))))
      else
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 1) (fun s => s.2.getD false)
              (.push (.inr 1) (fun _ => true)
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3)))))
            (.load (fun _ => (p.initial,none)) .halt))

def pure (k : p.K) (xs : List Bool) : Stacks p.K := Function.update (fun _ => []) k xs
lemma pure_at (k : p.K) (xs : List Bool) : pure p k xs k=xs := by simp [pure]
lemma pure_update (k : p.K) (xs ys : List Bool) :
    Function.update (pure p k xs) k ys=pure p k ys := Function.update_idem ..
lemma pure_nil (k : p.K) : pure p k []=fun _ => [] := by simp [pure]

def cfg (l : Label p) (s : Stacks p.K) (a b : List Bool) : (program p).machine.Cfg :=
  ⟨some l,(p.initial,none),mapStacks p s a b⟩
def done (ys : List Bool) : (program p).machine.Cfg :=
  ⟨none,(p.initial,none),mapStacks p (fun _ => []) [] ys⟩

def runCfg (ys : List Bool) (c : p.machine.Cfg) : (program p).machine.Cfg :=
  ⟨c.l.elim (some (.inr 2)) (fun l => some (.inl l)),(c.var,none),mapStacks p c.stk [] ys⟩

lemma run_step (ys : List Bool) (s t : p.machine.Cfg) (h : p.machine.step s=some t) :
    (program p).machine.step (runCfg p ys s)=some (runCfg p ys t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none))
      Prod.fst (some (.inr 2)) (p.code l)) (v,none) (frameStacks stk ![[],ys]))=_
    rw [stepAux_frame _ _ _ (fun _ => rfl)]
    rfl

lemma parse_nil (a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a [])=
      some (cfg p (.inr 1) (fun _=>[]) a []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_false (xs a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a (false::xs))=
      some (cfg p (.inr 1) (fun _=>[]) a xs) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_one (a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a [true])=
      some (cfg p (.inr 1) (fun _=>[]) a []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_true (b : Bool) (xs a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a (true::b::xs))=
      some (cfg p (.inr 0) (fun _=>[]) (b::a) xs) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl
lemma restore_nil (xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) [] ys)=
      some (cfg p (.inl p.main) (pure p p.input xs) [] ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma restore_cons (b : Bool) (a xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) (b::a) ys)=
      some (cfg p (.inr 1) (pure p p.input (b::xs)) a ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,updLeft,pure_at,pure_update]; rfl
lemma reverse_nil (a ys : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output []) a ys)=
      some (cfg p (.inr 3) (fun _=>[]) a (false::ys)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd1,pure_nil]; rfl
lemma reverse_cons (b : Bool) (xs a ys : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output (b::xs)) a ys)=
      some (cfg p (.inr 2) (pure p p.output xs) (b::a) ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd0,pure_at,pure_update]; rfl
lemma encode_nil (ys : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (fun _=>[]) [] ys)=some (done p ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd0]; rfl
lemma encode_cons (b : Bool) (xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (fun _=>[]) (b::xs) ys)=
      some (cfg p (.inr 3) (fun _=>[]) xs (true::b::ys)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl

end MapLeft
end MetricKMedianRecovery.BitMachine

end OAI
