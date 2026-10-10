import OAI.Geometry.RCD.Sobolev.SquaredDistanceEnergy
import OAI.Geometry.RCD.Harmonic.CompressedRadialTime

namespace OAI

/-! # Cost and quadratic decrement of the actual radial contraction -/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem radial_contraction_moments (p : X) {R a : ℝ} (hR : 0 ≤ R)
    (ha : 0 ≤ a) (_ha1 : a ≤ 1)
    (heik : ∀ᵐ x ∂μ, x ∈ ball p R →
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1)
    (ν : Measure X) (hν : ν ≪ μ) (hsν : ∀ᵐ x ∂ν, x ∈ ball p R)
    (π : Measure C(Time, X)) (hinit : π.map (fun γ => γ 0) = ν)
    {C : ℝ≥0∞} (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hrad : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = a * dist (γ 0) p ∧
      dist (γ 1) p = (1 - a) * dist (γ 0) p) :
    (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) =
        a ^ 2 * weightedGradientSquare μ hQ ν (inwardQuadratic μ hQ p hR) ∧
      (∫ γ, SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p hR) (γ 0) -
        SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p hR) (γ 1) ∂π) =
        (a - a ^ 2 / 2) * weightedGradientSquare μ hQ ν (inwardQuadratic μ hQ p hR) := by
  let q := inwardQuadratic μ hQ p hR
  have hstart : ∀ᵐ γ ∂π, γ 0 ∈ ball p R := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rwa [hinit]
  have hrep (s : Time) : ∀ᵐ γ ∂π,
      SobolevSpace.toLp μ hQ q (γ s) =
        (inwardDistance p R (γ s)) ^ 2 / 2 - R * inwardDistance p R (γ s) := by
    apply ae_of_ae_map (measurable_path_eval s).aemeasurable
      (p := fun x => SobolevSpace.toLp μ hQ q x =
        (inwardDistance p R x) ^ 2 / 2 - R * inwardDistance p R x)
    exact (Measure.absolutelyContinuous_of_le_smul (hc s)).ae_le
      (inwardQuadratic_coe μ hQ p hR)
  have hmoment : (∫ γ, dist (γ 0) p ^ 2 ∂π) = weightedGradientSquare μ hQ ν q := by
    have hm : Measurable (fun x : X => dist x p ^ 2) := by fun_prop
    rw [← integral_map (measurable_path_eval 0).aemeasurable hm.aestronglyMeasurable, hinit,
      inwardQuadratic_weighted_energy μ hQ p hR heik ν hν hsν]
    simp only [dist_comm]
  constructor
  · rw [← hmoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hrad] with γ hγ
    rw [hγ.1, mul_pow]
  · rw [← hmoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hrad, hstart, hrep 0, hrep 1] with γ hγ hstart h0 h1
    have hd0 : dist p (γ 0) < R := by simpa only [mem_ball, dist_comm] using hstart
    have hd1 : dist p (γ 1) < R := by
      rw [dist_comm, hγ.2]
      exact (mul_le_of_le_one_left dist_nonneg (by linarith : 1 - a ≤ 1)).trans_lt
        (by simpa only [dist_comm] using hd0)
    rw [h0, h1]
    simp only [inwardDistance, max_eq_left (sub_nonneg.mpr hd0.le),
      max_eq_left (sub_nonneg.mpr hd1.le)]
    rw [dist_comm p (γ 1), hγ.2, dist_comm p (γ 0)]
    ring

end RegularPointCoordinates

end OAI
