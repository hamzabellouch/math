import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Form
import OAI.Combinatorics.KMedianRecovery.Recovery.Stack

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

section Length
variable {K A S : Type} [DecidableEq K] [Fintype K]

def stackLength (stk : Stacks K) : ℕ := ∑ k, (stk k).length

def pushBound : TM2.Stmt (fun _ : K => Bool) A S → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

lemma stackLength_pure (k : K) (bits : List Bool) :
    stackLength (Function.update (fun _ => []) k bits) = bits.length := by
  simp [stackLength,Function.update_apply,apply_ite]

lemma stackLength_update_le (stk : Stacks K) (k : K) (bits : List Bool) (d : ℕ)
    (h : bits.length ≤ (stk k).length+d) :
    stackLength (Function.update stk k bits) ≤ stackLength stk + d := by
  have he : (fun j => (Function.update stk k bits j).length) =
      Function.update (fun j => (stk j).length) k bits.length := by
    funext j
    simp only [Function.update_apply]
    split <;> rfl
  unfold stackLength
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hs := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (s := Finset.univ)
    (f := fun j => (stk j).length) (Finset.mem_univ k)
  omega

lemma stepAux_length (stmt : TM2.Stmt (fun _ : K => Bool) A S) (s : S) (stk : Stacks K) :
    stackLength (TM2.stepAux stmt s stk).stk ≤ stackLength stk + pushBound stmt := by
  induction stmt generalizing s stk with
  | push k f q ih =>
    apply (ih s (Function.update stk k (f s :: stk k))).trans
    have hl := stackLength_update_le stk k (f s :: stk k) 1 (by simp)
    change _ ≤ _ + (pushBound q+1)
    omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    apply (ih _ (Function.update stk k (stk k).tail)).trans
    have hl := stackLength_update_le stk k (stk k).tail 0 (by simp)
    change _ ≤ _ + pushBound q
    omega
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    simp only [TM2.stepAux,pushBound]
    cases hf : f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact (ihr _ _).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact (ihq _ _).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp only [TM2.stepAux,pushBound,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushBound,Nat.add_zero,le_refl]

end Length

noncomputable def Program.maxPush (p : Program) : ℕ := Finset.univ.sup (fun l => pushBound (p.code l))

lemma Program.step_length (p : Program) (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    stackLength t.stk ≤ stackLength s.stk + p.maxPush := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    have hb : pushBound (p.code l) ≤ p.maxPush :=
      Finset.le_sup (f := fun l => pushBound (p.code l)) (Finset.mem_univ l)
    exact (stepAux_length (p.code l) v stk).trans (Nat.add_le_add_left hb _)

lemma iterate_length {S : Type} (f : S → Option S) (len : S → ℕ) (c : ℕ)
    (h : ∀ s t, f s = some t → len t ≤ len s+c) (n : ℕ) (s t : S)
    (he : (fun x : Option S => x.bind f)^[n] (some s) = some t) :
    len t ≤ len s+n*c := by
  induction n generalizing s with
  | zero =>
    have ht : s = t := Option.some.inj he
    subst t
    omega
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he
    change (fun x : Option S => x.bind f)^[n] (f s) = some t at he
    cases hf : f s with
    | none =>
      rw [hf,Function.iterate_fixed rfl n] at he
      contradiction
    | some u =>
      have hi := ih u (by simpa only [hf] using he)
      have hs := h s u hf
      simp only [Nat.succ_mul]
      omega

lemma Program.output_length (p : Program) {x y : List Bool} {m : ℕ}
    (h : TM2OutputsInTime p.machine x (some y) m) :
    y.length ≤ x.length+m*p.maxPush := by
  have hl := iterate_length p.machine.step (fun s => stackLength s.stk) p.maxPush
    p.step_length h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  simp only [initList_bool,haltList_bool,stackLength_pure] at hl
  exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_right p.maxPush h.steps_le_m) _)

structure PolyComputes (f : List Bool → List Bool) where
  program : Program
  time : Polynomial ℕ
  outputs : ∀ x, TM2OutputsInTime program.machine x (some (f x)) (time.eval x.length)

noncomputable def PolyComputes.toTM2 {f : List Bool → List Bool} (h : PolyComputes f) :
    Turing.TM2ComputableInPolyTime id id f where
  tm := h.program.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := h.time
  outputsFun x := by simpa using h.outputs x

lemma polynomial_monotone (P : Polynomial ℕ) : Monotone (fun n => P.eval n) := by
  intro n m h
  simp only [Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

noncomputable def PolyComputes.comp {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (g ∘ f) where
  program := Composition.program hf.program hg.program
  time := hg.time.comp (Polynomial.X + hf.time * Polynomial.C hf.program.maxPush) + hf.time
  outputs x := by
    have hlen := hf.program.output_length (hf.outputs x)
    have hh := Composition.outputs hf.program hg.program (hf.outputs x) (hg.outputs (f x))
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X]
    exact Nat.add_le_add_right (polynomial_monotone hg.time hlen) _

end MetricKMedianRecovery.BitMachine

end OAI
