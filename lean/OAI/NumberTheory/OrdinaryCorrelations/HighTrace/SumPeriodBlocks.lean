import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.PeriodicOrigin
open Finset Classical Filter

lemma sum_period_blocks (M : ℕ) (f : ℕ → ℝ) (hp : Function.Periodic f M) (q : ℕ) :
    (∑ n ∈ range (M*q), f n) = (q : ℝ) * ∑ n ∈ range M, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    have he : (∑ n ∈ range M, f (M*q+n)) = ∑ n ∈ range M, f n := by
      apply sum_congr rfl
      intro n hn
      simpa only [Nat.nsmul_eq_mul,Nat.mul_comm,Nat.add_comm] using hp.nsmul q n
    rw [he,Nat.cast_add,Nat.cast_one]
    ring

lemma sum_period_quotient (M N : ℕ) (f : ℕ → ℝ) (hp : Function.Periodic f M) :
    (∑ n ∈ range N, f n) = (N/M : ℕ) * (∑ n ∈ range M, f n) + ∑ n ∈ range (N%M), f n := by
  have hN : N = M*(N/M)+N%M := (Nat.div_add_mod N M).symm
  conv_lhs => rw [hN,sum_range_add,sum_period_blocks M f hp]
  congr 1
  apply sum_congr rfl
  intro n hn
  simpa only [Nat.nsmul_eq_mul,Nat.mul_comm,Nat.add_comm] using hp.nsmul (N/M) n

theorem discrepancy (M N : ℕ) (hM : 0 < M) (f : ℕ → ℝ) (hp : Function.Periodic f M) :
    |(∑ n ∈ range N, f n) - (N : ℝ) * ((∑ n ∈ range M, f n)/(M : ℝ))| ≤
      2 * ∑ n ∈ range M, |f n| := by
  let A := ∑ n ∈ range M, f n
  let K := ∑ n ∈ range M, |f n|
  have hK : 0 ≤ K := sum_nonneg (fun _ _ => abs_nonneg _)
  have hA : |A| ≤ K := abs_sum_le_sum_abs _ _
  have hR : |∑ n ∈ range (N%M), f n| ≤ K := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mod_lt N hM).le)
    intro n hn ho
    exact abs_nonneg _
  have hq : (N : ℝ) = (M : ℝ)*(N/M : ℕ)+(N%M : ℕ) := by
    exact_mod_cast (Nat.div_add_mod N M).symm
  have hmR : (0 : ℝ) < M := by exact_mod_cast hM
  have hrlo : (0 : ℝ) ≤ (N%M : ℕ) := Nat.cast_nonneg _
  have hrhi : (N%M : ℕ) / (M : ℝ) ≤ 1 := (div_le_one hmR).mpr (by exact_mod_cast (Nat.mod_lt N hM).le)
  have he : (N/M : ℕ)*A - (N : ℝ)*(A/(M : ℝ)) = -((N%M : ℕ)/(M : ℝ)*A) := by
    rw [hq]
    field_simp
    ring
  rw [sum_period_quotient M N f hp]
  calc
    _ = |(∑ n ∈ range (N%M), f n) - ((N%M : ℕ)/(M : ℝ)*A)| := by
      congr 1
      dsimp only [A] at he ⊢
      linarith
    _ ≤ |∑ n ∈ range (N%M), f n| + |((N%M : ℕ)/(M : ℝ)*A)| := abs_sub _ _
    _ ≤ K+K := by
      apply add_le_add hR
      rw [abs_mul,abs_of_nonneg (div_nonneg hrlo hmR.le)]
      exact (mul_le_mul_of_nonneg_left hA (div_nonneg hrlo hmR.le)).trans
        ((mul_le_mul_of_nonneg_right hrhi hK).trans_eq (one_mul K))
    _ = _ := by dsimp only [K]; ring

end OrdinaryCorrelations.PeriodicOrigin

end

end OAI
