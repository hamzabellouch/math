import OAI.Geometry.RCD.Sobolev.ScalarDimensionalBochner

namespace OAI

/-! # The integrated Bakry--Ledoux estimate for scalar Bochner inequalities

Erbar--Kuwada--Sturm, arXiv:1303.4382v2, Definition 4.6, equation (4.10),
and Theorem 4.8. This is its bounded-weight integrated specialization on
functions with an L² weak Laplacian. The Laplacian commutes with heat, so
its term is written as heat applied to the actual weak source.

The finite-dimensional term is retained in the weak Bochner formula.
-/

open Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

def IntegratedBakryLedoux (K N : ℝ) : Prop :=
  ∃ c : ℝ → ℝ, Tendsto c (𝓝[>] 0) (𝓝 1) ∧
    ∀ (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ), IsWeakLaplacian μ hQ u d →
    ∀ (w : Lp ℝ 2 μ) (C : ℝ≥0), 0≤w → (∀ᵐ x ∂μ, |w x|≤C) →
    ∀ (t : ℝ) (ht : 0<t),
      (∫ x, w x*(SobolevSpace.minimalSlope μ hQ
        (heatSobolev μ hQ t ht (SobolevSpace.toLp μ hQ u)) x)^2 ∂μ)+
      (2*t/N)*c t*(∫ x, w x*(heatAt μ hQ t d x)^2 ∂μ) ≤
        Real.exp (-2*K*t)*(∫ x, heatAt μ hQ t w x*
          (SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ)

end RegularPointCoordinates

end

end OAI
