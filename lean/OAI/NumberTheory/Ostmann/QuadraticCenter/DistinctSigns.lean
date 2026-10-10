import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctGenerating

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators Polynomial

theorem sum_signs_eq_counts {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1) :
    (∑ i ∈ I, (y i : ℝ)) =
      ((I.filter (fun i => y i = 1)).card : ℝ) -
      ((I.filter (fun i => y i = -1)).card : ℝ) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    have hyI : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1 :=
      fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hrec := ih hyI
    rcases hy a (Finset.mem_insert_self _ _) with h | h | h <;>
      simp [Finset.sum_insert ha, Finset.filter_insert, h, ha, hrec] <;> ring

theorem distinctGenerating_neg_coeff {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ) (k : ℕ) :
    (distinctGenerating I (fun i => -y i)).coeff k =
      (-1 : ℝ) ^ k * (distinctGenerating I y).coeff k := by
  rw [distinctGenerating_coeff, distinctGenerating_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard := (Finset.mem_powersetCard.mp hs).2
  simp only [Int.cast_neg, Finset.prod_neg, hcard]

theorem distinctGenerating_error_neg {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ) (k : ℕ) :
    |(k.factorial : ℝ) * (distinctGenerating I (fun i => -y i)).coeff k -
      (∑ i ∈ I, ((-y i : ℤ) : ℝ)) ^ k| =
    |(k.factorial : ℝ) * (distinctGenerating I y).coeff k -
      (∑ i ∈ I, (y i : ℝ)) ^ k| := by
  rw [distinctGenerating_neg_coeff]
  simp only [Int.cast_neg, Finset.sum_neg_distrib]
  rw [neg_pow (∑ i ∈ I, (y i : ℝ)) k]
  rw [show (k.factorial : ℝ) * ((-1 : ℝ) ^ k * (distinctGenerating I y).coeff k) -
    (-1 : ℝ) ^ k * (∑ i ∈ I, (y i : ℝ)) ^ k =
      (-1 : ℝ) ^ k * ((k.factorial : ℝ) * (distinctGenerating I y).coeff k -
        (∑ i ∈ I, (y i : ℝ)) ^ k) by ring]
  rw [abs_mul, abs_pow]
  simp

end Ostmann.QuadraticCenter

end OAI
