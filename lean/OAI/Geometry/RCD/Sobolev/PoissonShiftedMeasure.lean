import OAI.Geometry.RCD.Sobolev.LocalPoissonDimensionalDensity
import OAI.Geometry.RCD.Sobolev.PoissonSecondOrderData

namespace OAI

/-! # Shifted positivity for any actual full Poisson energy measure -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_measure_shifted_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (κ : ℝ) (hK : -κ≤K) (p : X) {r : ℝ} (hr : 0<r)
    (L : ℝ≥0) (U : Euclidean (n+2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n+2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) (U v) (ell v))
    (hL : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x≤(L:ℝ)^2*‖v‖^2)
    (M : PositiveBilinearMeasure X (Euclidean (n+2)))
    (hM : ∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) :
    ∀ v b, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*r)),
      2*b*ell v-(n:ℝ)*b^2≤((M.measure v).rnDeriv (hausdorff n X) x).toReal := by
  intro v b
  let E := Classical.choice (hM v)
  have hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) E.energy
      ((2:ℝ) • (M.measure v).toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic (U v) (U v))) := by
    rw [M.measure_toSignedMeasure]
    exact E.measure_laplacian
  apply hX.local_poisson_shifted_density hn hscalar (U v) (ell v) κ hK hr (hU v)
    (L*‖v‖₊) _ E.energy (M.measure v) E.representative hσ b
  simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hL v

end RegularPointCoordinates

end

end OAI
