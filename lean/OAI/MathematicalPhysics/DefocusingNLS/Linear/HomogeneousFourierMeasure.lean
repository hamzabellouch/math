import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzFourierPolynomial
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # The Fourier measure of the manuscript's homogeneous Hilbert space

Its L² norm is exactly the sum of the two homogeneous Sobolev energies,
with the radian Plancherel factor (2π)^(-12). The measure is locally finite
and has temperate growth, which permits the library's Schwartz density theorem.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFourierWeight (a k : ℝ) (ξ : E) : ℝ :=
  ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * (‖ξ‖ ^ (2 * (6 - a)) + ‖ξ‖ ^ (2 * k))

noncomputable def homogeneousFourierMeasure (a k : ℝ) : Measure E :=
  volume.withDensity (fun ξ => ENNReal.ofReal (homogeneousFourierWeight a k ξ))

theorem homogeneousFourierWeight_nonneg (a k : ℝ) (ξ : E) :
    0 ≤ homogeneousFourierWeight a k ξ := by unfold homogeneousFourierWeight; positivity

theorem homogeneousFourierWeight_pos (a k : ℝ) (ξ : E) (hξ : ξ ≠ 0) :
    0 < homogeneousFourierWeight a k ξ := by
  unfold homogeneousFourierWeight
  exact mul_pos (by positivity) (add_pos_of_pos_of_nonneg
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) _) (by positivity))

theorem continuous_homogeneousFourierWeight (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (homogeneousFourierWeight a k) := by
  have hlow : Continuous (fun ξ : E => ‖ξ‖ ^ (2 * (6 - a))) :=
    continuous_norm.rpow_const (fun _ => Or.inr (by linarith))
  have hhigh : Continuous (fun ξ : E => ‖ξ‖ ^ (2 * k)) :=
    continuous_norm.rpow_const (fun _ => Or.inr (by linarith))
  exact continuous_const.mul (hlow.add hhigh)

theorem homogeneousFourierMeasure_locallyFinite (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    IsLocallyFiniteMeasure (homogeneousFourierMeasure a k) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (continuous_homogeneousFourierWeight a k ha1 hk)

theorem homogeneousFourierMeasure_openPos (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    (homogeneousFourierMeasure a k).IsOpenPosMeasure := by
  have hn : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by
    simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton _
  have hd : ∀ᵐ ξ : E ∂volume, ENNReal.ofReal (homogeneousFourierWeight a k ξ) ≠ 0 := by
    filter_upwards [hn] with ξ hξ
    exact (ENNReal.ofReal_pos.mpr (homogeneousFourierWeight_pos a k ξ hξ)).ne'
  exact (withDensity_absolutelyContinuous'
    (continuous_homogeneousFourierWeight a k ha1 hk).measurable.ennreal_ofReal.aemeasurable
    hd).isOpenPosMeasure

private theorem homogeneousFourierWeight_le (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (ξ : E) :
    homogeneousFourierWeight a k ξ ≤
      (2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹) * (1 + ‖ξ‖) ^ (2 * k) := by
  have hlow : ‖ξ‖ ^ (2 * (6 - a)) ≤ (1 + ‖ξ‖) ^ (2 * k) := by
    exact (Real.rpow_le_rpow (norm_nonneg ξ) (by linarith) (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (by linarith))
  have hhigh : ‖ξ‖ ^ (2 * k) ≤ (1 + ‖ξ‖) ^ (2 * k) :=
    Real.rpow_le_rpow (norm_nonneg ξ) (by linarith) (by linarith)
  unfold homogeneousFourierWeight
  calc
    _ ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        ((1 + ‖ξ‖) ^ (2 * k) + (1 + ‖ξ‖) ^ (2 * k)) := by gcongr
    _ = _ := by ring

/-- The exact Fourier measure has the growth property required for Schwartz density. -/
theorem homogeneousFourierMeasure_temperate (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    (homogeneousFourierMeasure a k).HasTemperateGrowth := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * k + 13)
  refine ⟨⟨N, ?_⟩⟩
  have hbase : Integrable (fun ξ : E => (1 + ‖ξ‖) ^ (-(13 : ℝ))) := by
    apply integrable_one_add_norm
    norm_num
  have hmajor := hbase.const_mul (2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹)
  have hweighted : Integrable (fun ξ : E => homogeneousFourierWeight a k ξ *
      (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
    have hp : Continuous (fun ξ : E => (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
      (continuous_const.add continuous_norm).rpow_const (fun ξ => Or.inl (by
        change 1 + ‖ξ‖ ≠ 0
        positivity))
    apply hmajor.mono' ((continuous_homogeneousFourierWeight a k ha1 hk).mul hp).aestronglyMeasurable
    filter_upwards [] with ξ
    change ‖homogeneousFourierWeight a k ξ * (1 + ‖ξ‖) ^ (-(N : ℝ))‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (homogeneousFourierWeight_nonneg a k ξ) (Real.rpow_nonneg (by positivity) _))]
    calc
      _ ≤ ((2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹) * (1 + ‖ξ‖) ^ (2 * k)) *
          (1 + ‖ξ‖) ^ (-(N : ℝ)) := mul_le_mul_of_nonneg_right
        (homogeneousFourierWeight_le a k ha ha1 hk ξ) (by positivity)
      _ = (2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹) *
          (1 + ‖ξ‖) ^ (2 * k - N) := by
        rw [mul_assoc, ← Real.rpow_add (by positivity)]
        congr 2
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (by linarith))
        (by positivity)
  unfold homogeneousFourierMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (continuous_homogeneousFourierWeight a k ha1 hk).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul] using hweighted

end DefocusingNLS

end OAI
