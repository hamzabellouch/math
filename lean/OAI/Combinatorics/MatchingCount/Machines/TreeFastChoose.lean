import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps
import OAI.Combinatorics.MatchingCount.Complexity.TreeNumericCosts

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

def fastChoose : Realizer (fun x : ℕ×ℕ=>x.1.choose x.2) :=
  (choose (composition (pair second first) leNat) natChoose (constant 0)).congr (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    split_ifs with h
    · rfl
    · exact (Nat.choose_eq_zero_of_lt (by omega)).symm)
lemma fastChoose_work : WorkBound fastChoose (fun x=>x.1+weight x) := by
  obtain ⟨p,hp⟩:=natChoose_numeric_work
  let F := composition (pair (second (A:=ℕ) (B:=ℕ)) first) leNat
  have hF : PolynomialTime F := polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_leNat
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=polynomial_constant (A:=ℕ×ℕ) (0:ℕ)
  refine ⟨p.comp (2*X)+q+r+7*X+18,fun x=>?_⟩
  have hq':=(hq x).trans (polynomial_eval_monotone q (show weight x≤x.1+weight x by omega))
  have hr':=(hr x).trans (polynomial_eval_monotone r (show weight x≤x.1+weight x by omega))
  simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change F.cost x+(if decide (x.2≤x.1) then natChoose.cost x else (constant (A:=ℕ×ℕ) (0:ℕ)).cost x)+
    7*weight x+18+weight (x.1.choose x.2)≤_
  simp only [decide_eq_true_eq]
  by_cases h : x.2≤x.1
  · rw [ite_eq_left h]
    have hp':=(hp x).trans (polynomial_eval_monotone p (show x.1+x.2≤2*(x.1+weight x) by omega))
    dsimp only at hq' hr' hp'
    omega
  · rw [ite_eq_right h,Nat.choose_eq_zero_of_lt (show x.1<x.2 by omega)]
    dsimp only at hq' hr'
    omega

lemma polynomial_boundedFastChoose {A : Type} [Codec A] {f : A → ℕ×ℕ} {F : Realizer f}
    (hF : PolynomialTime F) (p : Polynomial ℕ)
    (hn : ∀ a,(f a).1≤p.eval (weight a)) : PolynomialTime (composition F fastChoose) := by
  obtain ⟨q,hq⟩:=hF
  apply work_composition ⟨q,hq⟩ fastChoose_work (p+q)
  intro a
  have h1:=hn a
  have h2:=hq a
  simp only [Polynomial.eval_add]
  omega
end MatchingFPRAS.TreeTyped

end OAI
