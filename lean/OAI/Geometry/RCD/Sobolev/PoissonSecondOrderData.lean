import OAI.Geometry.RCD.Coordinates.PoissonBilinearMeasure
import OAI.Geometry.RCD.Sobolev.LocalPoissonHessianPairing

namespace OAI

/-! # Poisson measure and Hessian data on a finite span

The common full measure and local integrated Hessian pairings follow from the
RCD structure. Shifted-square and dimension trace estimates control their mass.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_second_order_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (κ : ℝ) (hK : -κ≤K) (p : X) {r : ℝ} (hr : 0<r)
    (L : ℝ≥0) (U : Euclidean (n+2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n+2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) (U v) (ell v))
    (hL : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ (L:ℝ)^2*‖v‖^2) :
    ∃ M : PositiveBilinearMeasure X (Euclidean (n+2)),
      (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) ∧
      ∀ (v w : Euclidean (n+2)) (t : ℝ), t≤2*r →
        Nonempty (LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) (U v) (U w)) := by
  obtain ⟨M,hM⟩ := hX.poisson_bilinear_energy_measure hn κ hK p hr L U ell hU hL
  refine ⟨M,hM,?_⟩
  intro v w t ht
  apply hX.local_poisson_hessian_pairing hn (U v) (U w) (ell v) (ell w) hr ht
    (hU v) (hU w) (L*‖v‖₊) (L*‖w‖₊)
  · simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hL v
  · simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hL w

end RegularPointCoordinates

end

end OAI
