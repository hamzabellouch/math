import OAI.Geometry.RCD.Sobolev.BoundedSquareLaplacian
import OAI.Geometry.RCD.Sobolev.BoundedSquareVariation

namespace OAI

/-! # The heat-square pairing identity

The weak square rule identifies the derivative contributed by the moving
heat weight. All squares and Laplacians below are actual L² elements.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

/-- Move the heat generator from a weight to a bounded Sobolev square. -/
theorem heat_square_inner_laplacian (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (C L : ℝ≥0) (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    (hd : IsWeakLaplacian μ hQ u d) (w : Lp ℝ 2 μ) (s : ℝ) (hs : 0 < s) :
    inner ℝ (-heatGeneratorAt μ hQ s w)
        (boundedLpSquare μ (SobolevSpace.toLp μ hQ u) C C.coe_nonneg hu) =
      2*∫ x, heatAt μ hQ s w x*(SobolevSpace.toLp μ hQ u x*d x+
        (SobolevSpace.minimalSlope μ hQ u x)^2) ∂μ := by
  obtain ⟨q,hq,hrep⟩ := exists_weakLaplacian_square μ hQ u d C L hu hg hd
  have hsq : boundedLpSquare μ (SobolevSpace.toLp μ hQ u) C C.coe_nonneg hu =
      SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ u C) := by
    apply Lp.ext
    filter_upwards [boundedLpSquare_coe μ (SobolevSpace.toLp μ hQ u) C C.coe_nonneg hu,
      SobolevSpace.square_coe μ hQ u C hu] with x hx hy
    exact hx.trans hy.symm
  rw [hsq,heatGeneratorAt_of_pos μ hQ s hs,inner_neg_left,
    ← heatGenerator_form,energyForm_comm,hq,neg_neg,L2.inner_def]
  simp only [Real.inner_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  simp only [hx,heatSobolev_toLp]
  ring

end RegularPointCoordinates

end

end OAI
