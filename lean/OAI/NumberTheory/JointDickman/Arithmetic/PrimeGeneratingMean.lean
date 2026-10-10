import OAI.NumberTheory.JointDickman.Arithmetic.DivisorProductMean
import OAI.NumberTheory.JointDickman.Amplification.FloorErrors

namespace OAI

/-! # Finite generating functions for distinct prime factors -/
namespace JointDickman
open Finset

noncomputable def primeGeneratingAverage (P : Finset ℕ) (z : ℕ → ℝ) (N : ℕ) : ℝ := by
  classical
  exact (∑ n ∈ Ioc 0 N, ∏ p ∈ P, if p ∣ n then z p else 1)/(N : ℝ)

noncomputable def boundedPrimeSubsets (P : Finset ℕ) (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N)

noncomputable def primeGeneratingModel (P : Finset ℕ) (z : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ D ∈ boundedPrimeSubsets P N, (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ)

theorem primeGeneratingAverage_floor (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) (N : ℕ) :
    primeGeneratingAverage P z N = ∑ D ∈ P.powerset,
      (∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) := by
  classical
  have heq (n : ℕ) : (∏ p ∈ P, if p ∣ n then z p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0 := by
    convert divisor_product_expansion P hP (fun p => z p-1) n using 1
    simp
  simp only [primeGeneratingAverage,heq]
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro D _
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
  ring

theorem primeGeneratingAverage_truncated (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) (N : ℕ) :
    primeGeneratingAverage P z N = ∑ D ∈ boundedPrimeSubsets P N,
      (∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) := by
  classical
  rw [primeGeneratingAverage_floor P hP]
  symm
  apply sum_subset (filter_subset _ _)
  intro D hD hnot
  have hbig : N < ∏ p ∈ D, p := by simpa only [boundedPrimeSubsets,mem_filter,hD,true_and,not_le] using hnot
  simp only [Nat.div_eq_of_lt hbig,Nat.cast_zero,mul_zero,zero_div]

theorem primeGeneratingModel_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (hcoef : ∀ D ∈ boundedPrimeSubsets P N, |∏ p ∈ D, (z p-1)| ≤ C) :
    |primeGeneratingAverage P z N - primeGeneratingModel P z N| ≤
      C * ((boundedPrimeSubsets P N).card : ℝ)/(N : ℝ) := by
  classical
  rw [primeGeneratingAverage_truncated P hP,primeGeneratingModel,← sum_sub_distrib]
  calc
    _ ≤ ∑ D ∈ boundedPrimeSubsets P N,
        |(∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) -
          (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D ∈ boundedPrimeSubsets P N, C/(N : ℝ) := by
      apply sum_le_sum
      intro D hD
      have hDP : D ⊆ P := mem_powerset.mp (mem_filter.mp hD).1
      have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (hDP hp)).pos)
      have he := normalized_division_error hN hd
      calc
        _ = |∏ p ∈ D, (z p-1)| *
            |((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) - 1/(∏ p ∈ D, p : ℕ)| := by
          rw [← abs_mul]
          congr 1
          ring
        _ ≤ C*(1/(N : ℝ)) := mul_le_mul (hcoef D hD) he (abs_nonneg _) hC
        _ = C/(N : ℝ) := by ring
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

end JointDickman

end OAI
