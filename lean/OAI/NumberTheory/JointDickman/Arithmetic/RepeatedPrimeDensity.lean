import OAI.NumberTheory.JointDickman.Amplification.BinCounts
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail

namespace OAI

/-! # Repeated large prime factors have vanishing density

This removes prime multiplicities when proving the finite-bin distribution
input from finite prime-divisor expansions.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def repeatedPrimeExceptions (Q : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun n => ∃ p ∈ Q, p^2 ∣ n)

theorem repeatedPrimeExceptions_card_le (Q : Finset ℕ) (N : ℕ) :
    (repeatedPrimeExceptions Q N).card ≤ ∑ p ∈ Q, N / p^2 := by
  classical
  have heq : repeatedPrimeExceptions Q N =
      Q.biUnion (fun p => (Ioc 0 N).filter (fun n => p^2 ∣ n)) := by
    ext n
    simp only [repeatedPrimeExceptions,mem_filter,mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ p ∈ Q, ((Ioc 0 N).filter (fun n => p^2 ∣ n)).card := card_biUnion_le
    _ = _ := by simp only [Nat.Ioc_filter_dvd_card_eq_div]

theorem repeatedPrimeExceptions_bound (Q : Finset ℕ) (N : ℕ)
    {K : ℕ} (hK : K ≠ 0) (hQ : ∀ p ∈ Q, K < p) :
    ((repeatedPrimeExceptions Q N).card : ℝ) ≤ (N : ℝ)/K := by
  have hcard : ((repeatedPrimeExceptions Q N).card : ℝ) ≤
      ∑ p ∈ Q, ((N / p^2 : ℕ) : ℝ) := by
    exact_mod_cast repeatedPrimeExceptions_card_le Q N
  calc
    _ ≤ ∑ p ∈ Q, ((N / p^2 : ℕ) : ℝ) := hcard
    _ ≤ ∑ p ∈ Q, (N : ℝ)/(p : ℝ)^2 := by
      apply sum_le_sum
      intro p _
      exact_mod_cast (Nat.cast_div_le (m := N) (n := p^2) :
        ((N / p^2 : ℕ) : ℝ) ≤ (N : ℝ)/(p^2 : ℕ))
    _ = (N : ℝ) * ∑ p ∈ Q, 1/(p : ℝ)^2 := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (N : ℝ) * (1/K) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail Q hK hQ) (Nat.cast_nonneg N)
    _ = _ := by ring

noncomputable def distinctBinCount (E : Finset ℕ) (n : ℕ) : ℕ := by
  classical
  exact (E.filter (fun p => p ∣ n)).card

theorem binCount_eq_distinct_of_no_squares (E : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) {n : ℕ} (hn : n ≠ 0)
    (hsq : ∀ p ∈ E, ¬p^2 ∣ n) : binCount E n = distinctBinCount E n := by
  classical
  simp only [binCount,distinctBinCount,card_eq_sum_ones,sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd]
    have hlo := (hE p hp).factorization_pos_of_dvd hn hd
    have hhi : ¬2 ≤ n.factorization p := by
      intro h
      exact hsq p hp (((hE p hp).pow_dvd_iff_le_factorization hn).mpr h)
    omega
  · rw [ite_eq_right hd]
    exact Nat.factorization_eq_zero_of_not_dvd hd

noncomputable def allLargeBinPrimes (J : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Ioc ⌊x^((1 : ℝ)/J)⌋₊ ⌊x⌋₊).filter Nat.Prime

theorem repeatedLargeBinPrimes_tendsto_zero {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      ((repeatedPrimeExceptions (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ)/(A*x))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x^((1 : ℝ)/J)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hK := tendsto_nat_floor_atTop.comp hpow
  have hKr : Tendsto (fun x : ℝ => (⌊x^((1 : ℝ)/J)⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hlim : Tendsto (fun x : ℝ => 1/(⌊x^((1 : ℝ)/J)⌋₊ : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hKr
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le (by linarith))
  filter_upwards [hK.eventually (eventually_ge_atTop 1),eventually_ge_atTop (1 : ℝ)] with x hKx hx
  change 1 ≤ ⌊x^((1 : ℝ)/J)⌋₊ at hKx
  have hxA : 0 < A*x := mul_pos hA (by linarith)
  have hbound := repeatedPrimeExceptions_bound (allLargeBinPrimes J x) ⌊A*x⌋₊
    (by omega : ⌊x^((1 : ℝ)/J)⌋₊ ≠ 0)
    (fun p hp => (mem_Ioc.mp (mem_filter.mp hp).1).1)
  calc
    _ ≤ ((⌊A*x⌋₊ : ℝ)/(⌊x^((1 : ℝ)/J)⌋₊ : ℝ))/(A*x) :=
      div_le_div_of_nonneg_right hbound hxA.le
    _ ≤ ((A*x)/(⌊x^((1 : ℝ)/J)⌋₊ : ℝ))/(A*x) := by
      gcongr
      exact Nat.floor_le hxA.le
    _ = _ := by field_simp

end JointDickman

end OAI
