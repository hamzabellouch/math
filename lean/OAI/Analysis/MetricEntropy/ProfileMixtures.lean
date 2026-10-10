import OAI.Analysis.MetricEntropy.Basic
import OAI.Analysis.MetricEntropy.GraphProfile
import OAI.Analysis.MetricEntropy.CompressionLevels
import Mathlib.Data.Fintype.BigOperators

namespace OAI

universe uX uY uι uLabel uJ

/-!
# Combining graph-ball levels using the actual logarithmic profile

The profile expansion and dilation estimate are applied to each actual extended
graph distance. The finite sums below retain disconnected distances, with no
extra finite-distance hypothesis. The final theorem combines the two losses
from column assignment and the one loss from rounding.
-/

noncomputable section

namespace MetricEntropyDuality.ProfileMixtures

open scoped BigOperators

variable {X : Type uX} {Y : Type uY} {ι : Type uι} {Label : ι → Type uLabel} [Fintype Y]

theorem sum_gamma_fin {h : ℕ} (hh : 0 < h) :
    (∑ j : Fin h, LogProfile.gamma h j.val) = 1 := by
  simpa only [Fin.sum_univ_eq_sum_range] using LogProfile.sum_gamma hh

/-- The actual nonnegative column mixture, before imposing any sign or mass
condition on its coefficients. -/
def profileMixture (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (h : ℕ) (μ : Y → ℝ) (x : X) : ℝ :=
  ∑ y, μ y * LogProfile.phi h (PartitionGraph.distance L (T y) x (v y))

private theorem ballIndicator_eq_distance (L : (i : ι) → X → Label i)
    (T : Finset ι) (j : ℕ) (x v : X) :
    CompressionLevels.ballIndicator L T j x v =
      if PartitionGraph.distance L T x v ≤ (j : ℕ∞) then (1 : ℝ) else 0 := by
  by_cases hd : PartitionGraph.distance L T x v ≤ (j : ℕ∞)
  · simp [CompressionLevels.ballIndicator, PartitionGraph.near, hd]
  · simp [CompressionLevels.ballIndicator, PartitionGraph.near, hd]

private theorem sum_weighted_levels {J : Type uJ} [Fintype J]
    (α : J → ℝ) (μ : Y → ℝ) (b : J → Y → ℝ) :
    (∑ j, α j * ∑ y, μ y * b j y) =
      ∑ y, μ y * ∑ j, α j * b j y := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The literal logarithmic profile is exactly the weighted sum of the original
graph-ball mixture at all levels. -/
theorem profileMixture_eq_sum (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) {h : ℕ} (hh : 0 < h) (μ : Y → ℝ) (x : X) :
    profileMixture L v T h μ x = ∑ j : Fin h,
      LogProfile.gamma h j.val * CompressionLevels.levelValue L v T μ j.val x := by
  unfold profileMixture CompressionLevels.levelValue
  rw [sum_weighted_levels]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => LogProfile.gamma h j *
    CompressionLevels.ballIndicator L (T y) j x (v y)) h]
  simpa only [ballIndicator_eq_distance] using
    LogProfile.phi_eq_sum_mul_indicator hh (PartitionGraph.distance L (T y) x (v y))

/-- With the actual graph-column index type, the mixture is the shared literal
`columnCombination`, rather than a separate abstract approximation predicate. -/
theorem profileMixture_columns [Fintype X]
    (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι)) (h : ℕ)
    (μ : GraphProfile.Columns X 𝒯 → ℝ) (x : X) :
    profileMixture L (fun y : GraphProfile.Columns X 𝒯 => y.1)
        (fun y => y.2.val) h μ x =
      columnCombination (GraphProfile.column L 𝒯 h) μ x := rfl

/-- The actual factor-three dilation bound survives mixing columns whose
nonnegative coefficients have total mass at most one. -/
theorem dilated_level_sum_le (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) {h : ℕ} (hh : 0 < h) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ) (x : X) :
    (∑ j : Fin h, LogProfile.gamma h j.val *
      CompressionLevels.levelValue L v T μ (3 * j.val + 2) x) ≤
        profileMixture L v T h μ x + θ := by
  unfold CompressionLevels.levelValue
  rw [sum_weighted_levels]
  calc
    (∑ y, μ y * ∑ j : Fin h, LogProfile.gamma h j.val *
        CompressionLevels.ballIndicator L (T y) (3 * j.val + 2) x (v y)) ≤
        ∑ y, μ y * (LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) + θ) := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hμ y)
      have hd : (∑ j : Fin h, LogProfile.gamma h j.val *
          CompressionLevels.ballIndicator L (T y) (3 * j.val + 2) x (v y)) ≤
            LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) +
              Real.log 3 / Real.log ((h : ℝ) + 1) := by
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => LogProfile.gamma h j *
          CompressionLevels.ballIndicator L (T y) (3 * j + 2) x (v y)) h]
        simpa only [ballIndicator_eq_distance] using
          LogProfile.dilation_mul_indicator hh (PartitionGraph.distance L (T y) x (v y))
      exact hd.trans (add_le_add (le_refl _) hprofile)
    _ = profileMixture L v T h μ x + (∑ y, μ y) * θ := by
      simp only [profileMixture, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ profileMixture L v T h μ x + θ := by
      apply add_le_add (le_refl _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hθ0

/-- Per-level assignment losses and rounding losses combine into the actual
one-sided profile bounds from uniform compression. -/
theorem rounded_level_sum_bounds (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) {h : ℕ} (hh : 0 < h) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (x : X) (assigned rounded : Fin h → ℝ)
    (hlower : ∀ j, CompressionLevels.levelValue L v T μ j.val x - 2 * θ ≤ assigned j)
    (hupper : ∀ j, assigned j ≤ CompressionLevels.levelValue L v T μ (3 * j.val + 2) x)
    (hround : ∀ j, 0 ≤ assigned j - rounded j ∧ assigned j - rounded j ≤ θ) :
    profileMixture L v T h μ x - 3 * θ ≤
        ∑ j : Fin h, LogProfile.gamma h j.val * rounded j ∧
      (∑ j : Fin h, LogProfile.gamma h j.val * rounded j) ≤
        profileMixture L v T h μ x + θ := by
  constructor
  · calc
      profileMixture L v T h μ x - 3 * θ =
          ∑ j : Fin h, LogProfile.gamma h j.val *
            (CompressionLevels.levelValue L v T μ j.val x - 3 * θ) := by
        rw [profileMixture_eq_sum L v T hh μ x]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          sum_gamma_fin hh, one_mul]
      _ ≤ ∑ j : Fin h, LogProfile.gamma h j.val * rounded j := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (LogProfile.gamma_nonneg hh j.val)
        have hlj := hlower j
        have hrj := (hround j).2
        linarith
  · calc
      (∑ j : Fin h, LogProfile.gamma h j.val * rounded j) ≤
          ∑ j : Fin h, LogProfile.gamma h j.val *
            CompressionLevels.levelValue L v T μ (3 * j.val + 2) x := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (LogProfile.gamma_nonneg hh j.val)
        have huj := hupper j
        have hrj := (hround j).1
        linarith
      _ ≤ profileMixture L v T h μ x + θ :=
        dilated_level_sum_le L v T μ hμ hmass hh hθ0 hprofile x

end MetricEntropyDuality.ProfileMixtures

end

end OAI
