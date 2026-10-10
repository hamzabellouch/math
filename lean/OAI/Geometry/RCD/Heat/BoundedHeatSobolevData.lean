import OAI.Geometry.RCD.Heat.BoundedHeatGram

namespace OAI

/-! # Bounds for the actual positive-time Sobolev heat representative -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem bounded_heat_sobolev_data (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t) :
    (∀ᵐ x ∂hausdorff n X,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x| ≤ A) ∧
    ∃ L : ℝ≥0, ∀ᵐ x ∂hausdorff n X,
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f)
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x ≤ (L:ℝ)^2 := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  constructor
  · simpa only [heatSobolev_toLp] using heatAt_abs_le_const μ Q t A f hf
  · obtain ⟨hlip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hf t ht
    have hrep : SobolevSpace.toLp μ Q (heatSobolev μ Q t ht f) =ᵐ[μ]
        kernelHeat μ Q hk t f := by
      simpa only [heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q hk ht f).symm
    have hgrad := SobolevSpace.minimalSlope_le_lipschitz μ Q
      (heatSobolev μ Q t ht f) hlip hrep
    refine ⟨⟨Real.sqrt ((A:ℝ)^2/(2*t*Real.exp (-2 * |K| * t))),Real.sqrt_nonneg _⟩,?_⟩
    filter_upwards [hgrad,localGamma_self μ Q (heatSobolev μ Q t ht f),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q (heatSobolev μ Q t ht f))]
        with x hx he h0
    rw [he]
    exact pow_le_pow_left₀ h0 hx 2

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
