import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctQuadraticMoment

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def signAverage {ι : Type*} (P : Finset ι) (y : ι → ℤ) : ℝ :=
  (∑ p ∈ P, (y p : ℝ)) / P.card

def distinctSignAverage {ι : Type*} [DecidableEq ι] (P : Finset ι) (y : ι → ℤ) (k : ℕ) : ℝ :=
  ((k.factorial : ℝ) * (∑ S ∈ P.powersetCard k, ∏ p ∈ S, (y p : ℝ))) / (P.card : ℝ) ^ k

theorem abs_signAverage_le_one {ι : Type*} (P : Finset ι) (hP : 0 < P.card)
    (y : ι → ℤ) (hy : ∀ p ∈ P, y p = -1 ∨ y p = 0 ∨ y p = 1) :
    |signAverage P y| ≤ 1 := by
  have hp : (0 : ℝ) < P.card := by exact_mod_cast hP
  rw [signAverage, abs_div, abs_of_pos hp, div_le_one hp]
  calc
    _ ≤ ∑ p ∈ P, |(y p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp'
      rcases hy p hp' with h | h | h <;> simp only [h] <;> norm_num
    _ = _ := by simp

theorem distinctSignAverage_error {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (hP : 0 < P.card) (y : ι → ℤ)
    (hy : ∀ p ∈ P, y p = -1 ∨ y p = 0 ∨ y p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) :
    |distinctSignAverage P y k - signAverage P y ^ k| ≤
      (((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card) *
        (|signAverage P y| + (k : ℝ) / Real.sqrt (P.card : ℝ)) ^ (k - 2) :=
  distinct_subset_normalized_error_bound P y hy hP hk heven

end Ostmann.QuadraticCenter

end

end OAI
