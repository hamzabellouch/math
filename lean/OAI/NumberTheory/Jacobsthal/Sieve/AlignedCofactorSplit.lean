import OAI.NumberTheory.Jacobsthal.Partitions.SourceLabelCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def alignedPrimeFactors (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : Finset ℕ :=
  qf.primeFactors.filter (aligns a r)

noncomputable def alignedPrimeProduct (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : ℕ :=
  ∏ p ∈ alignedPrimeFactors a r qf,p

noncomputable def alignedCofactor (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : ℕ :=
  qf/badPrimeProduct a r qf

theorem badPrimeProduct_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : 0 < badPrimeProduct a r qf :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem alignedPrimeProduct_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : 0 < alignedPrimeProduct a r qf :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem aligned_bad_product (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedPrimeProduct a r qf*badPrimeProduct a r qf = qf := by
  rw [alignedPrimeProduct,alignedPrimeFactors,badPrimeProduct,badPrimeFactors,
    Finset.prod_filter_mul_prod_filter_not,Nat.prod_primeFactors_of_squarefree hq]

theorem alignedCofactor_eq_product (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor a r qf = alignedPrimeProduct a r qf := by
  unfold alignedCofactor
  nth_rw 1 [← aligned_bad_product a r qf hq]
  exact Nat.mul_div_cancel _ (badPrimeProduct_pos a r qf)

theorem alignedCofactor_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    0 < alignedCofactor a r qf := by
  rw [alignedCofactor_eq_product a r qf hq]
  exact alignedPrimeProduct_pos a r qf

theorem alignedCofactor_mul_bad (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor a r qf*badPrimeProduct a r qf = qf := by
  rw [alignedCofactor_eq_product a r qf hq]
  exact aligned_bad_product a r qf hq

theorem alignedCofactor_coprime_den (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor a r qf).Coprime r.den := by
  rw [alignedCofactor_eq_product a r qf hq]
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  obtain ⟨hpf,halign⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hpf
  exact hprime.coprime_iff_not_dvd.mpr (aligned_prime_not_dvd_den a r hprime halign)

theorem alignedCofactor_coprime_bad (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor a r qf).Coprime (badPrimeProduct a r qf) := by
  rw [alignedCofactor_eq_product a r qf hq]
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  obtain ⟨hpf,halign⟩ := Finset.mem_filter.mp hp
  apply Nat.coprime_prod_right_iff.mpr
  intro u hu
  obtain ⟨huf,hnon⟩ := Finset.mem_filter.mp hu
  apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpf) (Nat.prime_of_mem_primeFactors huf)).mpr
  intro he
  subst u
  exact hnon halign

end ErdosVarianceEffective

end

end Erdos970

end OAI
