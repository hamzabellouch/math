import OAI.Geometry.RCD.Heat.EventualHeatCumulative
import OAI.Geometry.RCD.Heat.DyadicHeatFamily

namespace OAI

/-! # Cumulative comparison for the actual heat family at small scales -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
  (M : PositiveBilinearMeasure X (Euclidean n))
  {p : X} {ρ Ccut : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ Ccut)

/-- No heat or small-mass bounds at the omitted coarse scales are needed.
In particular the cutoff may transition between the root ball and its
quarter ball, while all terms remain those of the original coordinate map. -/
theorem eventual_dyadic_heat_cumulative_comparison {R lambda ε C : ℝ}
    (hR : 0 < R) (hlambda : 0 < lambda) (hε : 0 ≤ ε) (hC : 0 ≤ C) (J : ℕ)
    (hstep : ∀ i, J ≤ i → ∀ v, ⟪v, dyadicHeatGram μ hQ hk U χ hR hlambda i v⟫_ℝ ≤
      (9 / 8 : ℝ) * ⟪v, dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) v⟫_ℝ)
    (hdecrement : ∀ i, J ≤ i → ∀ v,
      let d := ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ
      0 ≤ d ∧ ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤ C * d ∧
        d ≤ C * ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ)
    (hsmall : ∀ i, J ≤ i → ∀ v, ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤
      ε * ⟪v, dyadicHeatGram μ hQ hk U χ hR hlambda i v⟫_ℝ)
    (habsorb : 2 * C * (2 * geometricIntervalConstant ((3 / 4 : ℝ) * (9 / 8))) * ε ≤ 1 / 2) :
    ∃ A B D : ℝ, 0 < A ∧ 0 < B ∧ 0 < D ∧ ∀ (xi : Euclidean n) (k : ℕ),
      let Q := dyadicHeatGram μ hQ hk U χ hR hlambda
      let H := ⟪xi, (Q (J + k)).symm xi⟫_ℝ
      let mass := ∑ i ∈ Finset.range k,
        ⟪(Q (J + i)).symm xi, dyadicBochnerMass M n p R (J + i) ((Q (J + i)).symm xi)⟫_ℝ
      (∑ i ∈ Finset.range k,
        ⟪(Q (J + i)).symm xi, dyadicBochnerEnvelope M n p R (J + i) ((Q (J + i)).symm xi)⟫_ℝ) ≤ A * H ∧
      ‖xi‖ ^ 2 + mass ≤ B * H ∧ H ≤ D * (‖xi‖ ^ 2 + mass) := by
  exact eventual_heat_cumulative_comparison (dyadicHeatGram μ hQ hk U χ hR hlambda)
    (dyadicBochnerMass M n p R) (dyadicBochnerEnvelope M n p R) J
    (dyadicHeatGram_isPositive μ hQ hk U χ hR hlambda)
    (dyadicBochnerMass_isPositive M n p hR.le) hε hC hstep hdecrement hsmall
    (fun i v => (dyadicBochnerEnvelope_inner M n p R i v).le) habsorb

end RegularPointCoordinates

end

end OAI
