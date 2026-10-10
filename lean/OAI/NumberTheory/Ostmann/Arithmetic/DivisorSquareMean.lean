import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyLCM

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.DivisorSquareMean
open scoped BigOperators

lemma divisors_eq_bounded_filter {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hn, (Nat.le_of_dvd hn h.1).trans hnN⟩,h.1⟩
  · intro h
    exact ⟨h.2,hn.ne'⟩

lemma divisor_square_eq_double_sum {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors.card^2 = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      if d ∣ n ∧ e ∣ n then (1:ℕ) else 0 := by
  have heq : n.divisors.card^2 = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1:ℕ) := by
    simp [pow_two]
  rw [heq,divisors_eq_bounded_filter hn hnN]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hd' : d ∣ n
  · simp [hd']
  · simp [hd']

lemma sum_dvd_indicator (N k : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if k ∣ n then (1:ℕ) else 0) = N/k := by
  have hsets : (Finset.Icc 1 N).filter (fun n => k ∣ n) =
      (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ k ∣ n) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range,Nat.lt_succ_iff]
    omega
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [hsets]
  exact Nat.card_multiples' N k

theorem divisor_square_sum_eq (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, n.divisors.card^2) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, N/(d.lcm e) := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        if d ∣ n ∧ e ∣ n then (1:ℕ) else 0 := Finset.sum_congr rfl fun n hn =>
          divisor_square_eq_double_sum (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      simp_rw [← Nat.lcm_dvd_iff]
      exact sum_dvd_indicator N (d.lcm e)

theorem divisor_square_mean (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card:ℝ)^2) ≤
      (N:ℝ)*(1+Real.log N)^3 := by
  have heq : (∑ n ∈ Finset.Icc 1 N, (n.divisors.card:ℝ)^2) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ((N/(d.lcm e):ℕ):ℝ) := by
    exact_mod_cast divisor_square_sum_eq N
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (N:ℝ)/(d.lcm e) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact Nat.cast_div_le
    _ = (N:ℝ)*(∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ((d.lcm e:ℕ):ℝ)⁻¹) := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (FrequencyLCM.reciprocal_lcm_sum_le_log N)
      (Nat.cast_nonneg N)

end Ostmann.Arithmetic.DivisorSquareMean

end

end OAI
