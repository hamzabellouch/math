import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EvalTrans
import OAI.Combinatorics.KMedianRecovery.Recovery.Stack2

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma embedStacks_refl {K : Type} (s : Stacks K) : embedStacks (Function.Embedding.refl K) s = s := by
  funext k
  exact embedStacks_apply (Function.Embedding.refl K) s k

namespace While
variable (p : Program)

noncomputable abbrev program : Program where
  K := p.K
  input := p.input
  output := p.input
  Label := Option p.Label
  main := none
  State := p.State × Option Bool
  initial := (p.initial,none)
  code l := match l with
    | none => .peek p.input (fun _ b => (p.initial,b))
        (.branch (fun s => decide (s.2 = some true))
          (.load (fun _ => (p.initial,none)) (.goto (fun _ => some p.main)))
          (.load (fun _ => (p.initial,none)) .halt))
    | some l => renameStmt (Function.Embedding.refl p.K) some (fun s => (s,none)) Prod.fst
        (some none) (p.code l)

noncomputable def runCfg : p.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (Function.Embedding.refl p.K) some (fun s => (s,none)) (some none)
def controlCfg (x : List Bool) : (program p).machine.Cfg :=
  ⟨some none,(p.initial,none),Function.update (fun _ => []) p.input x⟩

lemma run_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p).machine.step (runCfg p s) = some (runCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (Function.Embedding.refl p.K) some (fun s => (s,none)) Prod.fst
      (some none) (p.code l)) (v,none) (embedStacks (Function.Embedding.refl p.K) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma initial (x : List Bool) : initList (program p).machine x = controlCfg p x := by
  rw [initList_bool]
  rfl

lemma start (x : List Bool) (h : x.head? = some true) :
    (program p).machine.step (controlCfg p x) = some (runCfg p (initList p.machine x)) := by
  rw [initList_bool]
  simp only [FinTM2.step,controlCfg,program,TM2.step,TM2.stepAux,Function.update_self,h,
    decide_true,Bool.cond_true,runCfg,renameCfg,Option.elim_some,embedStacks_refl]
  rfl

lemma stop (x : List Bool) (h : x.head? ≠ some true) :
    (program p).machine.step (controlCfg p x) = some (haltList (program p).machine x) := by
  rw [haltList_bool]
  simp only [FinTM2.step,controlCfg,program,TM2.step,TM2.stepAux,Function.update_self,h,
    decide_false,Bool.cond_false]
  rfl

lemma handoff (he : p.output = p.input) (x : List Bool) :
    runCfg p (haltList p.machine x) = controlCfg p x := by
  rw [haltList_bool]
  change (⟨some none,(p.initial,none),
    embedStacks (Function.Embedding.refl p.K) (Function.update (fun _ => []) p.output x)⟩ : (program p).machine.Cfg) = _
  rw [embedStacks_refl,he]
  rfl

noncomputable def advance {x y : List Bool} {m : ℕ} (he : p.output = p.input)
    (hstart : x.head? = some true) (h : TM2OutputsInTime p.machine x (some y) m) :
    EvalsToInTime (program p).machine.step (controlCfg p x) (some (controlCfg p y)) (m+1) := by
  have hh := iterate_transfer p.machine.step (program p).machine.step (runCfg p) (run_step p)
    h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  rw [handoff p he] at hh
  exact step_then (start p x hstart) ⟨⟨h.steps,hh⟩,h.steps_le_m⟩

def next (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if x.head? = some true then f x else x

lemma next_fixed (f : List Bool → List Bool) (x : List Bool) (h : x.head? ≠ some true) (n : ℕ) :
    (next f)^[n] x = x := Function.iterate_fixed (show next f x = x from ite_eq_right h) n

noncomputable def outputs (he : p.output = p.input) (f : List Bool → List Bool) (P : Polynomial ℕ)
    (hf : ∀ x, TM2OutputsInTime p.machine x (some (f x)) (P.eval x.length))
    (n B : ℕ) (x : List Bool)
    (hB : ∀ j ≤ n, ((next f)^[j] x).length ≤ B)
    (hstop : ((next f)^[n] x).head? ≠ some true) :
    EvalsToInTime (program p).machine.step (controlCfg p x)
      (some (haltList (program p).machine ((next f)^[n] x))) (n*(P.eval B+1)+1) := by
  induction n generalizing x with
  | zero => simpa only [Function.iterate_zero_apply,Nat.zero_mul,Nat.zero_add] using one_step (stop p x hstop)
  | succ n ih =>
    by_cases hx : x.head? = some true
    · have hnext : next f x = f x := ite_eq_left hx
      have hBn : ∀ j ≤ n, ((next f)^[j] (f x)).length ≤ B := by
        intro j hj
        have hh := hB (j+1) (Nat.add_le_add_right hj 1)
        simpa only [Function.iterate_succ_apply,hnext] using hh
      have hstopn : ((next f)^[n] (f x)).head? ≠ some true := by
        simpa only [Function.iterate_succ_apply,hnext] using hstop
      have hi := ih (f x) hBn hstopn
      have ha := advance p he hx (hf x)
      have hh := eval_trans ha hi
      have hlen : x.length ≤ B := hB 0 (Nat.zero_le _)
      have ht : P.eval x.length ≤ P.eval B := polynomial_monotone P hlen
      simp only [Function.iterate_succ_apply,hnext]
      exact time_mono hh (by simp only [Nat.succ_mul]; omega)
    · rw [next_fixed f x hx]
      exact time_mono (one_step (stop p x hx)) (by omega)

end While

noncomputable def PolyComputes.whileLoop {f : List Bool → List Bool} (hf : PolyComputes f)
    (fuel : List Bool → ℕ) (Q R : Polynomial ℕ)
    (hq : ∀ x, fuel x ≤ Q.eval x.length)
    (hr : ∀ x j, j ≤ fuel x → ((While.next f)^[j] x).length ≤ R.eval x.length)
    (hs : ∀ x, ((While.next f)^[fuel x] x).head? ≠ some true) :
    PolyComputes (fun x => (While.next f)^[fuel x] x) where
  program := While.program hf.sameIO.program
  time := Q*(hf.sameIO.time.comp R+1)+1
  outputs x := by
    have hh := While.outputs hf.sameIO.program rfl f hf.sameIO.time hf.sameIO.outputs (fuel x)
      (R.eval x.length) x (hr x) (hs x)
    change TM2OutputsInTime (While.program hf.sameIO.program).machine x
      (some ((While.next f)^[fuel x] x)) _
    unfold TM2OutputsInTime
    rw [While.initial]
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hq x)) 1

end MetricKMedianRecovery.BitMachine

end OAI
