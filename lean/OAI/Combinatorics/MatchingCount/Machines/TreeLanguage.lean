import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterStructured

namespace OAI

namespace MatchingFPRAS.RegisterStructured
open TreeData TreeMachine RegisterProc RegisterControl Turing MachineCost

variable {R : Type} [DecidableEq R]
lemma loop_nil (i : R) (P : Proc (K R)) (E : Env R) (hi : E i=.nil) :
    Exec (loop i P) (encodeEnv E) (encodeEnv E) 2 := by
  have hh : Runs (loopCode i P) (some Loop.halt) E E 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  exact compile_exec _ _ _ _ (Runs.step (M:=loopCode i P) Loop.test E _ E E 1 1
    (Effect.nilBranch _ _ _ _ hi) hh)
lemma loop_step (i : R) (P : Proc (K R)) (E F G : Env R) (n m : ℕ)
    (hi : E i≠.nil) (h : Exec P (encodeEnv E) (encodeEnv F) n)
    (ht : Exec (loop i P) (encodeEnv F) (encodeEnv G) m) :
    Exec (loop i P) (encodeEnv E) (encodeEnv G) (n+m+2) := by
  cases he : E i with
  | nil => exact False.elim (hi he)
  | cons x y =>
    obtain ⟨a,ha,hs⟩:=effect_compiles (loopCode i P) Loop.test (.branch i Loop.halt Loop.body) rfl
      E E (some Loop.body) 1 (Effect.consBranch _ _ _ _ x y he)
    obtain ⟨b,hb,hm⟩:=effect_compiles (loopCode i P) Loop.body (.call P Loop.test) rfl
      E F (some Loop.test) (n+1) (Effect.call _ _ _ _ n h)
    obtain ⟨c,hc,hg⟩:=ht
    change MachineCost.run (TM2.step (RegisterControl.code (loopCode i P))) c
      (RegisterControl.cfg _ (some Loop.test) F)=RegisterControl.cfg _ none G at hg
    refine ⟨a+b+c,by omega,?_⟩
    change MachineCost.run (TM2.step (RegisterControl.code (loopCode i P))) (a+b+c)
      (RegisterControl.cfg _ (some Loop.test) E)=RegisterControl.cfg _ none G
    rw [run_add,run_add,hs,hm,hg]
end MatchingFPRAS.RegisterStructured

namespace MatchingFPRAS.TreeLanguage
open TreeData TreeMachine RegisterProc RegisterStructured

variable {R : Type} [DecidableEq R]
inductive Program (R : Type) [DecidableEq R] where
  | leaf (P : Proc (K R))
  | seq (p q : Program R)
  | select (i : R) (nil cons : Program R)
  | loop (i : R) (body : Program R)

def compile : Program R → Proc (K R)
  | .leaf P => P
  | .seq p q => RegisterProc.seq (compile p) (compile q)
  | .select i p q => RegisterStructured.select i (compile p) (compile q)
  | .loop i p => RegisterStructured.loop i (compile p)

inductive Eval : Program R → Env R → Env R → ℕ → Prop
  | leaf (P E F n) (h : Exec P (encodeEnv E) (encodeEnv F) n) : Eval (.leaf P) E F n
  | seq (p q E F G n m) (h : Eval p E F n) (h' : Eval q F G m) : Eval (.seq p q) E G (n+m)
  | nilBranch (i p q E F n) (hi : E i=.nil) (h : Eval p E F n) : Eval (.select i p q) E F (n+3)
  | consBranch (i p q E F n) (hi : E i≠.nil) (h : Eval q E F n) : Eval (.select i p q) E F (n+3)
  | loopNil (i p E) (hi : E i=.nil) : Eval (.loop i p) E E 2
  | loopStep (i p E F G n m) (hi : E i≠.nil) (h : Eval p E F n)
      (ht : Eval (.loop i p) F G m) : Eval (.loop i p) E G (n+m+2)
  | weaken (p E F n m) (h : Eval p E F n) (hm : n ≤ m) : Eval p E F m

theorem compiles (p : Program R) (E F : Env R) (n : ℕ) (h : Eval p E F n) :
    Exec (compile p) (encodeEnv E) (encodeEnv F) n := by
  induction h with
  | leaf P E F n h => exact h
  | seq p q E F G n m h h' ih ih' => exact ih.seq ih'
  | nilBranch i p q E F n hi h ih => exact select_nil i _ _ E F n hi ih
  | consBranch i p q E F n hi h ih =>
    cases he : E i with
    | nil => exact False.elim (hi he)
    | cons x y => exact select_cons i _ _ E F n x y he ih
  | loopNil i p E hi => exact loop_nil i _ E hi
  | loopStep i p E F G n m hi h ht ih iht => exact loop_step i _ E F G n m hi ih iht
  | weaken p E F n m h hm ih => exact ih.mono hm

def clear (i : R) : Program R := .leaf (procedure (.nil i ()))
def copy (i j : R) (h : i≠j) : Program R := .leaf (procedure (.copy i j h ()))
def cons (i j : R) (h : i≠j) : Program R := .leaf (procedure (.cons i j h ()))
def split (i j : R) (h : i≠j) : Program R := .leaf (procedure (.split i j h ()))
lemma clear_eval (E : Env R) (i : R) :
    Eval (clear i) E (Function.update E i .nil) ((TreeData.encode (E i)).length+2) :=
  Eval.leaf _ _ _ _ (nil_exec E i ())
lemma copy_eval (E : Env R) (i j : R) (hij : i≠j) :
    Eval (copy i j hij) E (putPair E i j (E i) (E i))
      ((TreeData.encode (E j)).length+3*(TreeData.encode (E i)).length+4) :=
  Eval.leaf _ _ _ _ (copy_exec E i j hij ())
lemma cons_eval (E : Env R) (i j : R) (hij : i≠j) :
    Eval (cons i j hij) E (putPair E i j .nil (.cons (E i) (E j)))
      (2*(TreeData.encode (E i)).length+3) :=
  Eval.leaf _ _ _ _ (cons_exec E i j hij ())
lemma split_eval (E : Env R) (i j : R) (hij : i≠j) (x y : Data) (hj : E j=.cons x y) :
    Eval (split i j hij) E (putPair E i j x y)
      ((TreeData.encode (E i)).length+2*(TreeData.encode x).length+4) :=
  Eval.leaf _ _ _ _ (split_exec E i j hij () x y hj)
end MatchingFPRAS.TreeLanguage

end OAI
