import OAI.Probability.InvariantIsing.Spectral.SpectralGG

namespace OAI

/-! Compact deterministic centers without assuming constant finite self-overlap. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def spectralDiagonalCenter (b : ℝ) : ℝ := max 0 (min 1 b)

lemma spectralDiagonalCenter_mem (b : ℝ) : spectralDiagonalCenter b ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma abs_sub_spectralDiagonalCenter_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) :
    |x - spectralDiagonalCenter b| ≤ |x - b| := by
  by_cases hb : b ≤ 0
  · rw [spectralDiagonalCenter, min_eq_right (by linarith : b ≤ 1), max_eq_left hb,
      sub_zero, abs_of_nonneg hx.1, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - b)]
    linarith
  · by_cases hb' : 1 ≤ b
    · rw [spectralDiagonalCenter, min_eq_left hb', max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0), abs_of_nonpos (by linarith [hx.2] : x - b ≤ 0)]
      linarith
    · rw [spectralDiagonalCenter, min_eq_right (le_of_not_ge hb'), max_eq_right (le_of_not_ge hb)]

/-- Each deterministic center may be clipped to the geometrically allowed
interval before taking a subsequence. The true finite self-overlap remains
inside the integral and its error is no larger. -/
lemma spectralMonomial_clipped_self_deviation_le {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (b : Fin m → ℝ) (σ : Spin N) :
    |(∏ a, projectedOverlap U (I a) σ σ ^ d a) -
      ∏ a, spectralDiagonalCenter (b a) ^ d a| ≤
        ∑ a, (d a : ℝ) * |projectedOverlap U (I a) σ σ - b a| := by
  refine (spectralMonomial_self_deviation_le U I d (fun a => spectralDiagonalCenter (b a))
    (fun a => spectralDiagonalCenter_mem (b a)) σ).trans ?_
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left
    (abs_sub_spectralDiagonalCenter_le
      ⟨projectedOverlap_self_nonneg _ _ _, projectedOverlap_self_le_one _ _ _⟩ (b a))
    (Nat.cast_nonneg _)

end InvariantIsing

end

end OAI
