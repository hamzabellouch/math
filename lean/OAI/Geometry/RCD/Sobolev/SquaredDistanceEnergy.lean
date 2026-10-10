import OAI.Geometry.RCD.Metric.DistanceEikonal

namespace OAI

/-! # The actual local energy of the compact squared-distance primitive -/

open Set Metric MeasureTheory
open scoped NNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem inwardQuadratic_gamma_self (p : X) {R : ℝ} (hR : 0 ≤ R)
    (heik : ∀ᵐ x ∂μ, x ∈ ball p R →
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1) :
    ∀ᵐ x ∂μ, x ∈ ball p R →
      localGamma μ hQ (inwardQuadratic μ hQ p hR) (inwardQuadratic μ hQ p hR) x =
        dist p x ^ 2 := by
  let u := inwardSobolev μ hQ p R
  let q := inwardQuadratic μ hQ p hR
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ (⟨R, hR⟩ : ℝ≥0) := by
    filter_upwards [inwardSobolev_bounds μ hQ p hR] with x hx
    exact (abs_of_nonneg hx.1).symm ▸ hx.2
  filter_upwards [inwardQuadratic_gamma μ hQ p hR heik, inwardSobolev_coe μ hQ p R,
    localGamma_comm μ hQ u q,
    localGamma_sub_left μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ u ⟨R, hR⟩) (R • u) q,
    localGamma_smul_left μ hQ (1 / 2 : ℝ) (SobolevSpace.square μ hQ u ⟨R, hR⟩) q,
    localGamma_smul_left μ hQ R u q,
    localGamma_square μ hQ u q ⟨R, hR⟩ hb] with x hqu hu hc hs hhalf hscale hsq hx
  have hd : dist p x < R := by simpa only [mem_ball, dist_comm] using hx
  change localGamma μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ u ⟨R, hR⟩ - R • u) q x = _
  rw [hs, hhalf, hscale, hsq, hc, hqu hx, hu]
  simp only [inwardDistance, max_eq_left (sub_nonneg.mpr hd.le)]
  ring

theorem inwardQuadratic_weighted_energy (p : X) {R : ℝ} (hR : 0 ≤ R)
    (heik : ∀ᵐ x ∂μ, x ∈ ball p R →
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1)
    (ν : Measure X) (hν : ν ≪ μ) (hs : ∀ᵐ x ∂ν, x ∈ ball p R) :
    weightedGradientSquare μ hQ ν (inwardQuadratic μ hQ p hR) =
      ∫ x, dist p x ^ 2 ∂ν := by
  apply integral_congr_ae
  filter_upwards [hs, hν.ae_le (inwardQuadratic_gamma_self μ hQ p hR heik),
    hν.ae_le (localGamma_self μ hQ (inwardQuadratic μ hQ p hR))] with x hx hg he
  exact he.symm.trans (hg hx)

end RegularPointCoordinates

end OAI
