import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma work_pair {f : A → B} {g : A → C} {F : Realizer f} {G : Realizer g}
    {measure : A → ℕ} (hF : WorkBound F measure) (hG : WorkBound G measure)
    (u : Polynomial ℕ) (hu : ∀ a,weight a≤u.eval (measure a)) : WorkBound (pair F G) measure := by
  obtain ⟨p,hp⟩:=hF
  obtain ⟨q,hq⟩:=hG
  refine ⟨7*p+q+11*u+32,fun a=>?_⟩
  have h1:=hp a
  have h2:=hq a
  have h3:=hu a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  rw [weight_prod]
  change F.cost a+G.cost a+11*weight a+6*weight (f a)+31+(1+weight (f a)+weight (g a))≤_
  omega
omit [Codec C] in
lemma work_choose {f : A → Bool} {g h : A → B} {F : Realizer f} {G : Realizer g} {H : Realizer h}
    {measure : A → ℕ} (hF : WorkBound F measure) (hG : WorkBound G measure) (hH : WorkBound H measure)
    (u : Polynomial ℕ) (hu : ∀ a,weight a≤u.eval (measure a)) : WorkBound (choose F G H) measure := by
  obtain ⟨p,hp⟩:=hF
  obtain ⟨q,hq⟩:=hG
  obtain ⟨r,hr⟩:=hH
  refine ⟨p+q+r+7*u+18,fun a=>?_⟩
  have h1:=hp a
  have h2:=hq a
  have h3:=hr a
  have h4:=hu a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change F.cost a+(if f a then G.cost a else H.cost a)+7*weight a+18+
    weight (if f a then g a else h a)≤_
  cases f a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

omit [Codec A] [Codec B] [Codec C] in
lemma factorial_numeric_work : WorkBound factorial id := by
  unfold factorial
  apply work_congr
  apply work_boundedRepeat (work_of_polynomial (polynomial_pair polynomial_identity (polynomial_constant 1))
    (4*X+1) (fun n=>by simpa using weight_nat_numeric n)) polynomial_multiply X (4*X^2+5)
    (fun n k z=>k≤n ∧ z.size≤1+(n-k)*n)
  · intro n; simp
  · intro n; simp
  · intro n k hk z hz
    change k<n at hk
    have he : n-k=(n-(k+1))+1:=by omega
    have hh:=nat_size_mul (k+1) z
    have hb : (k+1).size≤n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    change k≤n ∧ ((k+1)*z).size≤1+(n-k)*n
    refine ⟨by omega,?_⟩
    have hbound : 1+(n-k)*n=1+(n-(k+1))*n+n := by rw [he]; ring
    rw [hbound]
    omega
  · intro n k z hz
    have hh:=weight_nat_le z
    have hm:=Nat.mul_le_mul_right n (Nat.sub_le n k)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_pow,id_eq]
    nlinarith

omit [Codec A] [Codec B] [Codec C] in
lemma pair_nat_weight_numeric (x : ℕ×ℕ) : weight x≤4*(x.1+x.2)+3 := by
  have h1:=weight_nat_numeric x.1
  have h2:=weight_nat_numeric x.2
  rw [←Prod.eta x,weight_prod]
  omega
omit [Codec A] [Codec B] [Codec C] in
lemma natChoose_numeric_work : WorkBound natChoose (fun x=>x.1+x.2) := by
  have ht : ∀ {f : ℕ×ℕ → ℕ} {F : Realizer f},PolynomialTime F → WorkBound F (fun x=>x.1+x.2) :=
    fun h=>work_of_polynomial h (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)
  have hb : ∀ {f : ℕ×ℕ → Bool} {F : Realizer f},PolynomialTime F → WorkBound F (fun x=>x.1+x.2) :=
    fun h=>work_of_polynomial h (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)
  have hpair : ∀ {f g : ℕ×ℕ → ℕ} {F : Realizer f} {G : Realizer g},
      WorkBound F (fun x=>x.1+x.2) → WorkBound G (fun x=>x.1+x.2) → WorkBound (pair F G) (fun x=>x.1+x.2) :=
    fun h1 h2=>work_pair h1 h2 (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)
  have hf : WorkBound (composition (first (A:=ℕ) (B:=ℕ)) factorial) (fun x=>x.1+x.2) :=
    work_composition (ht polynomial_first) factorial_numeric_work X (fun x=>by simp only [Polynomial.eval_X,id_eq]; omega)
  have hs : WorkBound (composition (second (A:=ℕ) (B:=ℕ)) factorial) (fun x=>x.1+x.2) :=
    work_composition (ht polynomial_second) factorial_numeric_work X (fun x=>by simp only [Polynomial.eval_X,id_eq]; omega)
  have hd : WorkBound (composition subtract factorial) (fun x=>x.1+x.2) :=
    work_composition (ht polynomial_subtract) factorial_numeric_work X (fun x=>by simp only [Polynomial.eval_X,id_eq]; omega)
  unfold natChoose
  apply work_congr
  exact work_choose
    (hb (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less))
    (work_then_polynomial (hpair hf (work_then_polynomial (hpair hs hd) polynomial_multiply)) polynomial_quotient)
    (work_choose (hb (polynomial_composition (polynomial_pair polynomial_first polynomial_second) polynomial_less))
      (ht (polynomial_constant 0)) (ht (polynomial_constant 1)) (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x))
    (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)

omit [Codec B] [Codec C] in
lemma polynomial_boundedFactorial {f : A → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,f a≤p.eval (weight a)) : PolynomialTime (composition F factorial) :=
  work_composition hF factorial_numeric_work p hn
omit [Codec B] [Codec C] in
lemma polynomial_boundedChoose {f : A → ℕ×ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,(f a).1+(f a).2≤p.eval (weight a)) : PolynomialTime (composition F natChoose) :=
  work_composition hF natChoose_numeric_work p hn
end MatchingFPRAS.TreeTyped

end OAI
