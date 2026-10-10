import OAI.NumberTheory.TotientAsymptotic.ShiftedResidues

namespace OAI

/-! The concrete multiplicative sieve density equals the exact residue proportion. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma shiftedRootCount_prod (b : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) :
    shiftedRootCount (∏ p ∈ S,p) b = ∏ p ∈ S,shiftedRootCount p b := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using shiftedRootCount_one b
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
    rw [Finset.prod_insert hp,shiftedRootCount_mul hprime.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS' q hq).ne_zero)) hcop,
      ih hS',Finset.prod_insert hp]

lemma shiftedRootCount_density (b d : ℕ) (hd : Squarefree d) :
    (shiftedRootCount d b:ℝ) = d*shiftedSieveDensity b d := by
  classical
  have hprod : ∏ p ∈ d.primeFactors,p = d := Nat.prod_primeFactors_of_squarefree hd
  have hcount : shiftedRootCount d b = ∏ p ∈ d.primeFactors,if p ∣ b then 1 else 2 := by
    conv_lhs => rw [← hprod]
    rw [shiftedRootCount_prod b d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    apply Finset.prod_congr rfl
    intro p hp
    let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact shiftedRootCount_prime p b
  have hdensity : shiftedSieveDensity b d =
      ∏ p ∈ d.primeFactors,if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ) :=
    ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero
  calc
    _ = ∏ p ∈ d.primeFactors,if p ∣ b then (1:ℝ) else 2 := by
      rw [hcount,Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> simp
    _ = ∏ p ∈ d.primeFactors,(p:ℝ)*(if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p:ℝ)≠0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      split_ifs <;> field_simp
    _ = _ := by
      rw [Finset.prod_mul_distrib,hdensity,← Nat.cast_prod,hprod]

end TotientAsymptotic

end

end OAI
