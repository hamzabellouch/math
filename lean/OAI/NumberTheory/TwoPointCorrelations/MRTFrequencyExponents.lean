import OAI.NumberTheory.TwoPointCorrelations.MRTAmplificationPower

namespace OAI

/-! The increasing prime-polynomial thresholds in MRT's multiscale
partition, indexed from zero to match `mrtFirstSmallBand`. -/

namespace TwoPointCorrelations

noncomputable def mrtFrequencyExponent (η : ℝ) (j : ℕ) : ℝ :=
  1 / 4 - η * (1 + 1 / (2 * ((j : ℝ) + 1)))

lemma mrtFrequencyExponent_zero (η : ℝ) :
    mrtFrequencyExponent η 0 = 1 / 4 - 3 * η / 2 := by
  unfold mrtFrequencyExponent
  norm_num
  ring

lemma mrtFrequencyExponent_bounds {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    1 / 4 - 3 * η / 2 ≤ mrtFrequencyExponent η j ∧
      mrtFrequencyExponent η j ≤ 1 / 4 - η := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hi : (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hi0 : (0 : ℝ) ≤ 1 / (2 * ((j : ℝ) + 1)) := by positivity
  unfold mrtFrequencyExponent
  constructor
  · have hh := mul_le_mul_of_nonneg_left hi hη
    nlinarith
  · have hh := mul_nonneg hη hi0
    nlinarith

lemma mrtFrequencyExponent_nonneg {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 6)
    (j : ℕ) : 0 ≤ mrtFrequencyExponent η j := by
  have hh := (mrtFrequencyExponent_bounds hη j).1
  linarith

lemma mrtFrequencyExponent_gap (η : ℝ) (j : ℕ) :
    mrtFrequencyExponent η (j + 1) - mrtFrequencyExponent η j =
      η / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  unfold mrtFrequencyExponent
  push_cast
  field_simp [h1, h2]
  ring

lemma mrtFrequencyExponent_gap_lower {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    η / (2 * ((j : ℝ) + 2) ^ 2) ≤
      mrtFrequencyExponent η (j + 1) - mrtFrequencyExponent η j := by
  rw [mrtFrequencyExponent_gap]
  apply div_le_div_of_nonneg_left hη (by positivity)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- After paying half of the threshold gap for the mixed-moment
factorial, the remaining exponential saving is still summable. -/
lemma mrt_frequency_gap_saving {η x : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) (j : ℕ) :
    2 * x * (mrtFrequencyExponent η j - mrtFrequencyExponent η (j + 1) +
      η / (4 * ((j : ℝ) + 2) ^ 2)) ≤ -η * x / (2 * ((j : ℝ) + 2) ^ 2) := by
  have hh := mul_le_mul_of_nonneg_left (mrtFrequencyExponent_gap_lower hη j)
    (show 0 ≤ 2 * x by positivity)
  have he : 2 * (η / (4 * ((j : ℝ) + 2) ^ 2)) =
      η / (2 * ((j : ℝ) + 2) ^ 2) := by
    field_simp
    ring
  rw [show -η * x / (2 * ((j : ℝ) + 2) ^ 2) =
      -x * (η / (2 * ((j : ℝ) + 2) ^ 2)) by ring]
  nlinarith

end TwoPointCorrelations

end OAI
