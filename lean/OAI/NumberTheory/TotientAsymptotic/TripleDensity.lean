import OAI.NumberTheory.TotientAsymptotic.TripleSieveModel

namespace OAI

/-! Exact multiplicative residue proportions for the three-form sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleRootCount_one (a b : ℕ) : tripleRootCount 1 a b = 1 := by
  rw [tripleRootCount_eq_count 1 a b (by norm_num),Nat.count_one]
  simp [tripleSievePolynomial]

lemma tripleRootCount_prod (a b : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) :
    tripleRootCount (∏ p ∈ S,p) a b = ∏ p ∈ S,tripleRootCount p a b := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tripleRootCount_one a b
  | @insert p S hp ih =>
    have hprime := hS p (Finset.mem_insert_self _ _)
    have hS' : ∀ q ∈ S,q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S,q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hprime.coprime_iff_not_dvd.mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hprime (hS' q hq)).mp hd
      exact hp (he ▸ hq)
    rw [Finset.prod_insert hp,tripleRootCount_mul hprime.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS' q hq).ne_zero)) hcop,
      ih hS',Finset.prod_insert hp]

lemma tripleRootCount_density (a b d : ℕ) (hd : Squarefree d) :
    (tripleRootCount d a b:ℝ) = d*tripleSieveDensity a b d := by
  classical
  have hprod : ∏ p ∈ d.primeFactors,p = d := Nat.prod_primeFactors_of_squarefree hd
  have hcount : tripleRootCount d a b = ∏ p ∈ d.primeFactors,tripleRootCount p a b := by
    conv_lhs => rw [← hprod]
    exact tripleRootCount_prod a b d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hdensity : tripleSieveDensity a b d =
      ∏ p ∈ d.primeFactors,(tripleRootCount p a b:ℝ)/p :=
    ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero
  calc
    _ = ∏ p ∈ d.primeFactors,(tripleRootCount p a b:ℝ) := by rw [hcount,Nat.cast_prod]
    _ = ∏ p ∈ d.primeFactors,(p:ℝ)*((tripleRootCount p a b:ℝ)/p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib,hdensity,← Nat.cast_prod,hprod]

end TotientAsymptotic

end

end OAI
