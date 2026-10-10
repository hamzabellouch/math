import OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareWindow
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicSummation

namespace OAI

/-! Splitting only the prime index into dyadic blocks. The cofactor
coefficient, including its full-prime-set denominator, stays fixed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def minorArcDyadicPrimes (P : Finset ℕ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => Nat.log 2 p = j)

lemma minor_arc_dyadic_primes_bounds (P : Finset ℕ) (j p : ℕ)
    (hp : p ∈ minorArcDyadicPrimes P j) (hp0 : 0 < p) :
    2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j :=
  minor_arc_dyadic_prime_bounds hp0 (mem_filter.mp hp).2

lemma minor_arc_bilinear_dyadic_partition (J P : Finset ℕ)
    (hJ : ∀ p ∈ P, Nat.log 2 p ∈ J) (M H d k : ℕ)
    (a c : ℕ → ℂ) (α : ℝ) :
    minorArcBilinearWindow P M H d a c α k =
      ∑ j ∈ J, minorArcBilinearWindow (minorArcDyadicPrimes P j) M H d a c α k := by
  unfold minorArcBilinearWindow
  have hp (m : ℕ) : (∑ j ∈ J, ∑ p ∈ minorArcDyadicPrimes P j,
      minorArcWindowTerm M (d * p) k H (c p) (α * p) m) =
      ∑ p ∈ P, minorArcWindowTerm M (d * p) k H (c p) (α * p) m :=
    sum_fiberwise_of_maps_to hJ _
  rw [sum_comm (s := J) (t := range M)]
  apply sum_congr rfl
  intro m _
  rw [← mul_sum, hp]

lemma minor_arc_bilinear_dyadic_cutoffs (J P : Finset ℕ)
    (hJ : ∀ p ∈ P, Nat.log 2 p ∈ J) (M H d k : ℕ) (N : ℕ → ℕ)
    (hM : ∀ p ∈ P, (k + H) / (d * p) < M)
    (hN : ∀ j ∈ J, ∀ p ∈ minorArcDyadicPrimes P j, (k + H) / (d * p) < N j)
    (a c : ℕ → ℂ) (α : ℝ) :
    minorArcBilinearWindow P M H d a c α k =
      ∑ j ∈ J, minorArcBilinearWindow (minorArcDyadicPrimes P j) (N j) H d a c α k := by
  rw [minor_arc_bilinear_dyadic_partition J P hJ]
  apply sum_congr rfl
  intro j hj
  exact minor_arc_bilinear_cutoff_eq (minorArcDyadicPrimes P j) M (N j) H d k
    (fun p hp => hM p (mem_filter.mp hp).1) (hN j hj) a c α

lemma minor_arc_bilinear_dyadic_sum_le (J P : Finset ℕ)
    (hJ : ∀ p ∈ P, Nat.log 2 p ∈ J) (X M H d : ℕ) (N : ℕ → ℕ)
    (hM : ∀ k ∈ range X, ∀ p ∈ P, (k + H) / (d * p) < M)
    (hN : ∀ j ∈ J, ∀ k ∈ range X, ∀ p ∈ minorArcDyadicPrimes P j,
      (k + H) / (d * p) < N j)
    (a c : ℕ → ℂ) (α : ℝ) :
    (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ≤
      ∑ j ∈ J, ∑ k ∈ range X,
        ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (N j) H d a c α k‖ := by
  calc
    _ ≤ ∑ k ∈ range X, ∑ j ∈ J,
        ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (N j) H d a c α k‖ := by
      apply sum_le_sum
      intro k hk
      rw [minor_arc_bilinear_dyadic_cutoffs J P hJ M H d k N
        (hM k hk) (fun j hj => hN j hj k hk)]
      exact norm_sum_le _ _
    _ = _ := sum_comm

end TwoPointCorrelations

end OAI
