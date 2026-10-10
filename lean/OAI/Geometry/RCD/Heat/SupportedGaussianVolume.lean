import OAI.Geometry.RCD.Heat.GaussianVolumeMoment
import OAI.Geometry.RCD.Heat.GaussianUpperHeatIncrement

namespace OAI

/-! # Gaussian integration of a bounded source on the working ball -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsLocallyFiniteMeasure μ]

/-- A compactly supported Gaussian source is controlled by upper volume
bounds in the original metric, with no global volume hypothesis. -/
theorem supported_gaussian_integral_le (n : ℕ) (x : X)
    {s R C D V : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 < D) (hV : 0 ≤ V)
    (N : ℕ) (hroot : (2 : ℝ) ^ N * s = R) {f : X → ℝ} (hf : Integrable f μ)
    (hpoint : ∀ z, f z ≤ C / s ^ n * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)))
    (hzero : ∀ z ∉ ball x R, f z = 0)
    (hvolume : ∀ j ≤ N, μ.real (ball x (2 ^ j * s)) ≤ V * (2 ^ j * s) ^ n) :
    (∫ z, f z ∂μ) ≤ C * V * gaussianVolumeMomentConstant n D⁻¹ := by
  let ν := μ.restrict (ball x R)
  have hfinite : IsFiniteMeasure ν := ⟨by
    change μ.restrict (ball x R) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact isBounded_ball.measure_lt_top⟩
  have hdisplace : ∀ a : ℝ, 0 ≤ a → ∀ z, a * s ≤ dist x z →
      f z ≤ C / s ^ n * Real.exp (-a ^ 2 / D) := by
    intro a ha z hz
    have hd := (sq_le_sq₀ (mul_nonneg ha hs.le) dist_nonneg).mpr hz
    have hh := div_le_div_of_nonneg_right hd (by positivity : 0 ≤ D * s ^ 2)
    have he : (a * s) ^ 2 / (D * s ^ 2) = a ^ 2 / D := by field_simp
    rw [he] at hh
    exact (hpoint z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hh))
      (div_nonneg hC (pow_pos hs n).le))
  have hb := integral_gaussian_shell_le_volume ν n x hs hC (inv_pos.mpr hD) hV N
    hf.integrableOn
    (fun j _ z hz => shell_bound_of_displacement x hs f hdisplace j hz)
    (fun z hz => hzero z (by rwa [hroot] at hz))
    (fun j hj => by
      change (μ.restrict (ball x R)).real (ball x (2 ^ j * s)) ≤ _
      rw [measureReal_restrict_apply measurableSet_ball]
      exact (measureReal_mono inter_subset_left isBounded_ball.measure_lt_top.ne).trans (hvolume j hj))
  have he : (∫ z, f z ∂ν) = ∫ z, f z ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rwa [he] at hb

end RegularPointCoordinates

end

end OAI
