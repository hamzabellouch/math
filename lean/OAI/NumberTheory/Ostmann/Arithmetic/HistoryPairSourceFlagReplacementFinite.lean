import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementUnnormalizedExact

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open PolynomialFlagReplacementFinite HistoryPairKernelReplacementUnnormalized HistoryPairKernelReplacement

theorem weighted_update_abs_sub_le {η : Type*} [Fintype η] [DecidableEq η]
    (S : η → Finset ℤ) (μ : η → ℤ → ℝ) (primes : Finset ℕ) (ν : ℕ → ℝ)
    (F G H : (η → ℤ) → ℕ → ℝ)
    (hμ : ∀i z,z∈S i → 0≤μ i z) (hν : ∀n∈primes,0≤ν n)
    (he : ∀x∈Fintype.piFinset S,∀n∈primes,(∏i,μ i (x i))≠0 → ν n≠0 →
      |F x n-G x n|≤4*H x n) :
    |(∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*F x n)-
      (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*G x n)| ≤
      4*(∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*H x n) := by
  classical
  have hid : (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*F x n)-
      (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*G x n) =
      ∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*(F x n-G x n) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [hid]
  apply (abs_product_prior_sum_le S μ primes ν hμ hν _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hx0 : (∏i,μ i (x i))=0
  · simp only [hx0,zero_mul,mul_zero,le_refl]
  · have hxpos : 0 ≤ ∏i,μ i (x i) := Finset.prod_nonneg (fun i _=>hμ i _ (Fintype.mem_piFinset.mp hx i))
    calc
      (∏i,μ i (x i))*(∑n∈primes,ν n*|F x n-G x n|) ≤
          (∏i,μ i (x i))*(∑n∈primes,ν n*(4*H x n)) := by
        apply mul_le_mul_of_nonneg_left _ hxpos
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : ν n=0
        · simp only [hn0,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (he x hx n hn hx0 hn0) (hν n hn)
      _ = 4*((∏i,μ i (x i))*∑n∈primes,ν n*H x n) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
