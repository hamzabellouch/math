import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.BoolPostCompiler
import OAI.Combinatorics.MatchingCount.Machines.PhysicalRestriction
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProcess

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream BoolPostCompiler

variable {Q : Type}

def liftBool (M : Table Bool Q) : Table Symbol Q := fun q a b=>
  (M q (down a) b).map (fun qa=>(qa.1,qa.2.map up))
def upCfg (c : Cfg Bool Q) : Cfg Symbol Q := ⟨c.state,c.tape.map up⟩
lemma tick_up (M : Table Bool Q) (c : Cfg Bool Q) (b : Bool) :
    tick (liftBool M) (upCfg c) b=upCfg (tick M c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some q =>
    simp only [tick,upCfg,liftBool,(show (T.map up).head=up T.head from rfl),down_up]
    cases e:M q T.head b with
    | none => rfl
    | some qa =>
      rcases qa with ⟨q',act⟩
      cases act with
      | move d => simp only [Option.map_some,TM0.Stmt.map,Tape.map_move]
      | write a => simp only [Option.map_some,TM0.Stmt.map,Tape.map_write]
lemma execute_up (M : Table Bool Q) (n : ℕ) (c : Cfg Bool Q) (b : Stream) :
    execute (liftBool M) n (upCfg c) b=upCfg (execute M n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_up,ih,execute]
lemma liftBool_supported (M : Table Bool Q) (S : Finset Q) (hS : Supported M S) :
    Supported (liftBool M) S := by
  intro q hq a b q' act he
  simp only [liftBool,Option.map_eq_some_iff] at he
  obtain ⟨⟨q'',act'⟩,h,e⟩:=he
  have hqq : q''=q':=congrArg Prod.fst e
  subst q''
  exact hS q hq (down a) b q' act' h
lemma up_init (q : Q) (input : List Bool) :
    upCfg (⟨some q,Tape.mk₁ input⟩ : Cfg Bool Q)=⟨some q,Tape.mk₁ (input.map up)⟩ := by
  simp only [upCfg,Tape.map_mk₁]
lemma Implements.up {α : Type} {M : Table Bool Q} {out : α → Cfg Bool Q}
    {c : Cfg Bool Q} {p : Experiment α} (h : Implements M out c p) :
    Implements (liftBool M) (fun a=>upCfg (out a)) (upCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih =>
    apply Implements.read
    intro b
    rw [tick_up]
    exact ih b
  | delay c d n p hs hr ih =>
    apply Implements.delay (upCfg c) (upCfg d) n p _ ih
    intro b
    rw [execute_up,hs]
end MatchingFPRAS.PhysicalPost

end OAI
