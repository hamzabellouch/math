import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Heat evolution of an L² weak Laplacian -/

open MeasureTheory

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatTail_laplacian_toLp (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) {t : ℝ} (ht : 0 < t) :
    SobolevSpace.toLp μ hQ (heatSobolevMap μ hQ (t / 2) (half_pos ht)
      (-heatGeneratorAt μ hQ (t - t / 2) (SobolevSpace.toLp μ hQ u))) =
        heatAt μ hQ t d := by
  rw [heatTail_deriv_toLp μ hQ (t / 2) (half_pos ht) _ t (by linarith)]
  exact ((heat_weakLaplacian_hasDerivAt μ hQ u d hd ht).unique
    (heatAt_hasDerivAt μ hQ t ht (SobolevSpace.toLp μ hQ u))).symm

theorem heatTail_laplacian_norm_le (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) {t : ℝ} (ht : 0 < t) :
    ‖SobolevSpace.toLp μ hQ (heatSobolevMap μ hQ (t / 2) (half_pos ht)
      (-heatGeneratorAt μ hQ (t - t / 2) (SobolevSpace.toLp μ hQ u)))‖ ≤ ‖d‖ := by
  rw [heatTail_laplacian_toLp μ hQ u d hd ht]
  simpa only [one_mul] using (heatAt μ hQ t).le_of_opNorm_le (heatAt_norm_le μ hQ t) d

end RegularPointCoordinates

end OAI
