import OAI.Geometry.RCD.Sobolev.LocalPoissonDimensionalDensity
import OAI.Geometry.RCD.Sobolev.LocalPoissonPairingBound
import OAI.Geometry.RCD.Sobolev.PoissonSecondOrderData
import OAI.Geometry.RCD.Sobolev.PoissonHessianInput

namespace OAI

/-! # The exact Poisson Hessian input reduced to scalar dimensional Bochner

All measures, representatives and Dirichlet Hessian pairings are constructed
from the RCD space. The sole remaining analytic premise in this reduction is
the scalar weak finite-dimensional Bochner inequality (Han, Theorem 3.3).
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_hessian_input_of_scalar {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n) :
    LocalPoissonHessianInput hX := by
  classical
  intro κ _ hK p r hr L U ell hU hL
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let : IsFiniteMeasure (μ.restrict (ball p (2*r))) := ⟨by
    simpa only [Measure.restrict_apply_univ,μ] using
      hX.finiteOnBounded (ball p (2*r)) isBounded_ball⟩
  obtain ⟨M,hM,hpair⟩ := hX.poisson_second_order_data hn κ hK p hr L U ell hU hL
  have hgrad (v) : ∀ᵐ x ∂μ.restrict (ball p (8*r)),
      localGamma μ hQ (U v) (U v) x≤(L*‖v‖₊:ℝ≥0)^2 := by
    simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hL v
  have hsource (v) : IsMeasureLaplacianOn μ hQ (ball p (2*r))
      (Classical.choice (hM v)).energy
      ((2:ℝ) • (M.measure v).toSignedMeasure-(2*κ) • μ.withDensityᵥ
        (localGamma μ hQ (U v) (U v))) := by
    rw [M.measure_toSignedMeasure]
    exact (Classical.choice (hM v)).measure_laplacian
  have hshift : ShiftedBochnerLowerBound M (μ.restrict (ball p (2*r))) ell n := by
    apply shiftedBochnerLowerBound_of_density μ M ell n
    intro v b
    exact hX.local_poisson_shifted_density hn hscalar (U v) (ell v) κ hK hr
      (hU v) (L*‖v‖₊) (hgrad v) (Classical.choice (hM v)).energy (M.measure v)
      (Classical.choice (hM v)).representative (hsource v) b
  refine ⟨M,hM,hshift,?_⟩
  intro v w t _ ht
  let G := Classical.choice (hpair v w t ht)
  refine ⟨G,?_⟩
  have hh := hX.local_poisson_hessian_pairing_bound_of_scalar hn hscalar
    (U v) (U w) (ell v) (ell w) κ hK hr ht (hU v) (hU w)
    (L*‖v‖₊) (L*‖w‖₊) (hgrad v) (hgrad w)
    (Classical.choice (hM v)).energy (M.measure v)
    (Classical.choice (hM v)).representative (hsource v) G
  simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hh

end RegularPointCoordinates

end

end OAI
