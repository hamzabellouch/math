import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeComputability

namespace OAI

section
namespace MinUncut.Costed
open Turing.ToPartrec

def iterBody (c : Code) : Code :=
  .case .zero' (.cons (.comp .succ .zero) (.cons .head (.comp c .tail)))
def iterCode (c : Code) : Code := .fix (iterBody c)

lemma run_iterBody_zero (c : Code) (v : List ℕ) :
    Runs (iterBody c) (0::v) (0::v) (2000*(magnitude (0::v)+1)) :=
  (run_caseZero rfl (run_zero v)).mono (by omega)

lemma run_iterBody_succ {c : Code} {v w : List ℕ} {B : ℕ}
    (h : Runs c v w B) (n : ℕ) :
    Runs (iterBody c) ((n+1)::v) (1::n::w)
      (B+2000*(magnitude ((n+1)::v)+magnitude w+1)) := by
  have h1 := run_comp (run_const_zero (n::v)) (run_succ [0])
  have hf := run_comp (run_tail (n::v)) h
  have hh := run_caseSucc (f:=.zero') (run_cons h1 (run_cons (run_head (n::v)) hf))
  apply hh.mono
  simp only [magnitude_nil,magnitude_cons,List.headI_cons]
  omega

lemma run_iter {c : Code} (f : List ℕ → List ℕ) (n : ℕ) (v : List ℕ) (M B : ℕ)
    (hs : ∀i≤n,magnitude (f^[i] v)≤M)
    (hf : ∀i<n,Runs c (f^[i] v) (f^[i+1] v) B) :
    Runs (iterCode c) (n::v) (f^[n] v) ((n+1)*(B+5000*(n+M+4))) := by
  let state := fun i => (n-i)::f^[i] v
  have hsize : ∀i≤n,magnitude (state i)≤n+M+1 := by
    intro i hi
    have := hs i hi
    simp only [state,magnitude_cons]
    omega
  have hstep : ∀i<n,Runs (iterBody c) (state i) (1::state (i+1))
      (B+4000*(n+M+2)) := by
    intro i hi
    have hn : n-i=(n-(i+1))+1 := by omega
    have hh := run_iterBody_succ (hf i hi) (n-(i+1))
    rw [← hn] at hh
    apply hh.mono
    have hsi := hs i (by omega)
    have hsj := hs (i+1) (by omega)
    simp only [magnitude_cons]
    omega
  have hdone : Runs (iterBody c) (state n) (0::f^[n] v)
      (B+4000*(n+M+2)) := by
    simp only [state,Nat.sub_self]

    apply (run_iterBody_zero c (f^[n] v)).mono
    have := hs n le_rfl
    simp only [magnitude_cons]; omega
  have hh := run_fix_bounded n (n+M+1) (B+4000*(n+M+2)) hsize hstep hdone
  change Runs (iterCode c) (n::v) (f^[n] v) _ at hh
  apply hh.mono
  apply Nat.mul_le_mul_left
  omega

end MinUncut.Costed

noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def iterate {f : List ℕ → List ℕ} (F : PolyProgram f) (p : Polynomial ℕ)
    (hs : ∀n v i, i≤n → magnitude (f^[i] v)≤p.eval (magnitude (n::v))) :
    PolyProgram (fun v=>f^[v.headI] v.tail) where
  code := iterCode F.code
  bound := p+(X+1)*(F.bound.comp p+C 5000*(X+p+4))+C 3000*(X+1)
  run v := by
    cases v with
    | nil =>
      obtain ⟨t,ht,hc⟩ := run_caseZero (f:=.zero') (g:=
        .cons (.comp .succ .zero) (.cons .head (.comp F.code .tail))) (v:=[]) rfl (run_zero [])
      refine ⟨_,?_,CodeRun.fixDone (u := [0]) hc rfl⟩
      simp only [magnitude_nil] at ht
      simp only [eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_one,eval_ofNat,magnitude_nil]
      omega
    | cons n v =>
      have hh := run_iter (c := F.code) f n v (p.eval (magnitude (n::v)))
        (F.bound.eval (p.eval (magnitude (n::v)))) (hs n v) (by
          intro i hi
          have h := F.run (f^[i] v)
          have h' : Runs F.code (f^[i] v) (f^[i+1] v) (F.bound.eval (magnitude (f^[i] v))) := by
            simpa only [Function.iterate_succ_apply'] using h
          exact h'.mono (evalNat_mono F.bound (hs n v i (by omega))))
      apply hh.mono
      simp only [eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_one,eval_ofNat]
      have hn : n≤ magnitude (n::v) := by simp only [magnitude_cons]; omega
      have h₁ : (n+1)*(F.bound.eval (p.eval (magnitude (n::v)))+
          5000*(n+p.eval (magnitude (n::v))+4)) ≤
          (magnitude (n::v)+1)*(F.bound.eval (p.eval (magnitude (n::v)))+
          5000*(magnitude (n::v)+p.eval (magnitude (n::v))+4)) := by gcongr
      omega
  size v := by
    cases v with
    | nil => simp
    | cons n v =>
      have hh := hs n v n le_rfl
      simp only [List.headI_cons,List.tail_cons,eval_add,eval_mul,eval_comp,
        eval_C,eval_X,eval_one,eval_ofNat]
      omega

def dynamic : PolyProgram (fun v=>[(v.tail.drop v.headI).headI]) where
  code := dynamicAt
  bound := C 3000*(X+1)^2
  run v := by
    cases v with
    | nil =>
      obtain ⟨t,ht,hc⟩ := run_caseZero (g:=.cons (.comp .succ .zero)
         (.cons .head (.comp .tail .tail))) (v:=[]) rfl (run_zero [])
      have hf : Runs dynamicDrop [] [] 100 := ⟨_,by simp only [magnitude_nil] at ht; omega,CodeRun.fixDone (u := [0]) hc rfl⟩
      exact (run_comp hf (run_head [])).mono (by norm_num [magnitude])
    | cons n v =>
      apply (run_dynamicAt n v).mono
      simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
      have hn : n+1≤ magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
      nlinarith
  size v := by
    have h := (magnitude_head (v.tail.drop v.headI)).trans
      ((magnitude_drop v.headI v.tail).trans (magnitude_tail v))
    simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
    nlinarith

end MinUncut.Costed.PolyProgram

end
end

end OAI
