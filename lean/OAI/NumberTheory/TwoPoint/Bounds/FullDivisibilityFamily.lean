import OAI.NumberTheory.TwoPoint.Bounds.FullDivisibility

namespace OAI

/-! Finite weighted summation of the full-divisibility cutoff errors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma full_divisibility_family_error {ι : Type*} (l : ℕ) [NeZero l] (b : ZMod l)
    (h : ℕ) (U : Finset ι) (u : ι → ℕ) (weight : ι → ℝ)
    (hweight : ∀ i ∈ U, 0 ≤ weight i) (hu : ∀ i ∈ U, 0 < u i)
    (hunit : ∀ i ∈ U, IsUnit (u i : ZMod l)) (X T η : ℝ)
    (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ i ∈ U, X * Real.exp (-η) ≤ T / u i)
    (hhi : ∀ i ∈ U, T / u i ≤ X) :
    ‖(∑ i ∈ U, (weight i : ℂ) *
        (positivePrefix (fullLiouvilleProfile l b (u i) h) ⌊T⌋₊ / (T : ℂ))) -
      ((∑ i ∈ U, weight i / (u i : ℝ) : ℝ) : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      (∑ i ∈ U, weight i / (u i : ℝ)) * (2 * η + 1 / X) := by
  let F := positivePrefix
    (fun n => progressionSequence liouville l b n * liouville (n + h)) ⌊X⌋₊ / (X : ℂ)
  have he : (∑ i ∈ U, (weight i : ℂ) *
      (positivePrefix (fullLiouvilleProfile l b (u i) h) ⌊T⌋₊ / (T : ℂ))) -
      ((∑ i ∈ U, weight i / (u i : ℝ) : ℝ) : ℂ) * F =
      ∑ i ∈ U, (weight i : ℂ) *
        ((positivePrefix (fullLiouvilleProfile l b (u i) h) ⌊T⌋₊ / (T : ℂ)) -
          (1 / (u i : ℂ)) * F) := by
    push_cast
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change ‖_ - _ * F‖ ≤ _
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ U, weight i * ((1 / (u i : ℝ)) * (2 * η + 1 / X)) := by
      apply sum_le_sum
      intro i hiU
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight i hiU)]
      exact mul_le_mul_of_nonneg_left
        (fullLiouvilleProfile_bin_error l b (u i) h (hu i hiU) (hunit i hiU) X T η hX hη
          (hlo i hiU) (hhi i hiU)) (hweight i hiU)
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      ring


end TwoPointCorrelations

end OAI
