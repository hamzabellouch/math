import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TM2Response

namespace OAI

section Inline_PCPTableauRun

namespace MetricKMedian.PCP.Tableau
open Function Relation

namespace Padded
variable {A : Type} (f : A → Option A)
def next (a : A) : A := (f a).getD a
lemma reaches (a : A) (n : ℕ) : StateTransition.Reaches f a ((next f)^[n] a) := by
  induction n with
  | zero => exact ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    cases h : f ((next f)^[n] a) with
    | none => simpa only [next,h,Option.getD_none] using ih
    | some b =>
      simp only [next,h,Option.getD_some]
      exact ih.tail h
lemma none_iterate (n : ℕ) : (flip Bind.bind f)^[n] (none : Option A)=none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl
lemma option_to_next (a b : A) (n : ℕ)
    (h : (flip Bind.bind f)^[n] (some a)=some b) : (next f)^[n] a=b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip Bind.bind f)^[n] (f a)=some b at h
    cases hf : f a with
    | none => rw [hf,none_iterate] at h; contradiction
    | some c =>
      simp only [next,hf,Option.getD_some]
      exact ih c (by simpa only [hf] using h)
lemma fixed (b : A) (h : f b=none) (n : ℕ) : (next f)^[n] b=b :=
  Function.iterate_fixed (by simp [next,h]) n
lemma bounded (a b : A) {T : ℕ} (h : StateTransition.EvalsToInTime f a (some b) T)
    (hb : f b=none) : (next f)^[T] a=b := by
  have he := option_to_next f a b h.steps h.evals_in_steps
  have ht : T=(T-h.steps)+h.steps := by have := h.steps_le_m; omega
  rw [ht,Function.iterate_add_apply,he,fixed f b hb]
lemma terminal_unique (a b c : A) (h : StateTransition.Reaches f a b)
    (h' : StateTransition.Reaches f a c) (hb : f b=none) (hc : f c=none) : b=c :=
  Part.mem_unique (StateTransition.mem_eval.mpr ⟨h,hb⟩) (StateTransition.mem_eval.mpr ⟨h',hc⟩)
lemma agrees (a b c : A) (n : ℕ) (hn : (next f)^[n] a=b) (hb : f b=none)
    (hc : f c=none) (h : StateTransition.EvalsTo f a (some c)) : b=c := by
  have hr0 := reaches f a n
  rw [hn] at hr0
  have hr1 := reaches f a h.steps
  rw [option_to_next f a c h.steps h.evals_in_steps] at hr1
  exact terminal_unique f a b c hr0 hr1 hb hc
end Padded

open Turing.TM2

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
omit [Fintype K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma advance_eq_padded : advance M=Padded.next (step M) := by
  funext c
  cases c with
  | mk l v S => cases l <;> rfl
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma run_length (c : Cfg Γ Λ σ) (n : ℕ) (k : K) :
    (((advance M)^[n] c).stk k).length≤(c.stk k).length+radius M*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := advance_length M ((advance M)^[n] c) k
    rw [Nat.mul_succ]
    omega
omit [Fintype K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma run_of_outputs {c d : Cfg Γ Λ σ} {T : ℕ}
    (h : StateTransition.EvalsToInTime (step M) c (some d) T) (hd : d.l=none) :
    (advance M)^[T] c=d := by
  rw [advance_eq_padded]
  apply Padded.bounded _ _ _ h
  cases d with
  | mk l v S => simp only at hd; subst l; rfl
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRun

end OAI
