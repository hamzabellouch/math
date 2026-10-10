import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeNumericCosts

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

lemma nat_fold_size_bound (f : ℕ×ℕ → ℕ) (K M : ℕ)
    (hf : ∀ a b,(f (a,b)).size≤a.size+b.size+K) (as : List ℕ) (z : ℕ)
    (ha : ∀ a∈as,a.size≤M) :
    (as.foldl (fun z a=>f (a,z)) z).size≤z.size+as.length*(M+K) := by
  induction as generalizing z with
  | nil => simp
  | cons a as ih =>
    have hh:=hf a z
    have ha':=ha a (by simp)
    have ht:=ih (f (a,z)) (fun a h=>ha a (by simp [h]))
    simp only [List.foldl_cons,List.length_cons]
    nlinarith
lemma polynomial_nat_fold {f : ℕ×ℕ → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (K : ℕ) (hf : ∀ a b,(f (a,b)).size≤a.size+b.size+K) : PolynomialTime (fold F) := by
  apply polynomial_fold hF (4*X+4*X*(X+Polynomial.C K)+1)
  intro as z pre post he
  let S:=weight (as,z)
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; rw [weight_prod]; omega))
  have ha : ∀ a∈pre,a.size≤S := by
    intro a ha
    exact (size_le_weight a).trans ((weight_mem (as := as) (by simp [he,ha])).trans (by dsimp [S]; rw [weight_prod]; omega))
  have hz : z.size≤S := (size_le_weight z).trans (by dsimp [S]; rw [weight_prod]; omega)
  have hb:=nat_fold_size_bound f K S hf pre z ha
  have hw:=weight_nat_le (pre.foldl (fun z a=>f (a,z)) z)
  have hm:=Nat.mul_le_mul_right (S+K) hp
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one]
  change _≤4*S+4*S*(S+K)+1
  nlinarith
lemma polynomial_listSum : PolynomialTime listSum := by
  unfold listSum
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
    (polynomial_nat_fold polynomial_add 1 (fun a b=>(nat_size_add a b).trans (by omega)))
lemma polynomial_listProd : PolynomialTime listProd := by
  unfold listProd
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1))
    (polynomial_nat_fold polynomial_multiply 0 (fun a b=>by simpa using nat_size_mul a b))

lemma pairingStep_fold_size (as : List ℕ) (a b M : ℕ) (ha : ∀ i∈as,i.size≤M) :
    max (as.foldl (fun z i=>pairingStep (i,z)) (a,b)).1.size
      (as.foldl (fun z i=>pairingStep (i,z)) (a,b)).2.size ≤
      max a.size b.size+as.length*(M+2) := by
  induction as generalizing a b with
  | nil => simp
  | cons i as ih =>
    have hi:=ha i (by simp)
    have hsmall:=nat_size_add i 1
    have he : Nat.size 1=1:=by decide
    have hm:=nat_size_mul (i+1) a
    have hmax : max i.size 1≤M+1:=max_le (by omega) (by omega)
    have hstep : max b.size ((i+1)*a).size ≤ max a.size b.size+(M+2) := by
      rw [he] at hsmall
      have h1:=le_max_left a.size b.size
      have h2:=le_max_right a.size b.size
      exact max_le (by omega) (by omega)
    have ht:=ih b ((i+1)*a) (fun j h=>ha j (by simp [h]))
    simp only [pairingStep] at ht
    simp only [List.foldl_cons,List.length_cons,pairingStep]
    nlinarith
lemma polynomial_pairingFold : PolynomialTime (fold
    (pair (composition (second (A:=ℕ) (B:=ℕ×ℕ)) second)
      (composition (pair (composition first successor) (composition second first)) multiply))) := by
  apply polynomial_fold (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_successor)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_multiply)) (8*X+8*X*(X+2)+3)
  rintro as ⟨a,b⟩ pre post he
  let S:=weight (as,(a,b))
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have ha : ∀ i∈pre,i.size≤S := by
    intro i hi
    exact (size_le_weight i).trans ((weight_mem (as := as) (by simp [he,hi])).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have hab : max a.size b.size≤S := by
    have hh:=size_le_weight a
    have hh':=size_le_weight b
    apply max_le <;> dsimp [S] <;> simp only [weight_prod] <;> omega
  let z:=pre.foldl (fun z i=>pairingStep (i,z)) (a,b)
  have hm:=pairingStep_fold_size pre a b S ha
  have h1:=weight_nat_le z.1
  have h2:=weight_nat_le z.2
  have h3:=le_max_left z.1.size z.2.size
  have h4:=le_max_right z.1.size z.2.size
  change max z.1.size z.2.size≤_ at hm
  have hmul:=Nat.mul_le_mul_right (S+2) hp
  change weight z≤_
  rw [←Prod.eta z,weight_prod]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤8*S+8*S*(S+2)+3
  nlinarith
lemma pairingNumber_numeric_work : WorkBound pairingNumber id := by
  unfold pairingNumber
  apply work_congr
  apply work_then_polynomial _ polynomial_first
  apply work_then_polynomial _ polynomial_pairingFold
  exact work_pair range_numeric_work
    (work_of_polynomial (polynomial_constant (1,0)) (4*X+1) (fun n=>by simpa using weight_nat_numeric n))
    (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
lemma polynomial_boundedPairingNumber {A : Type} [Codec A] {f : A → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,f a≤p.eval (weight a)) : PolynomialTime (composition F pairingNumber) :=
  work_composition hF pairingNumber_numeric_work p hn
end MatchingFPRAS.TreeTyped

end OAI
