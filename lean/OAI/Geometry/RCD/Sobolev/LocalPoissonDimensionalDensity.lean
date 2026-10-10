import OAI.Geometry.RCD.Sobolev.LocalPoissonShiftedHessian
import OAI.Geometry.RCD.Metric.RationalInteriorBalls

namespace OAI

/-! # Finite-dimensional density bound for the actual Poisson measure

This is a consequence of the scalar weak Bochner inequality of Han,
Theorem 3.3. Countable compact exhaustion retains the prescribed full
measure and proves the density bound on the whole interior ball.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_dimensional_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c κ : ℝ) (hK : -κ≤K)
    {p : X} {r : ℝ} (hr : 0<r)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (L : ℝ≥0)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f f)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      ((2:ℝ) • σ.toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic f f))) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*r)),
      c^2≤(n:ℝ)*(σ.rnDeriv (hausdorff n X) x).toReal := by
  rw [ball_eq_iUnion_rational_closedBall p (2*r)]
  apply (ae_restrict_iUnion_iff _ _).mpr
  intro q
  obtain ⟨_,_,_,_,hdim,_⟩ := hX.local_poisson_shifted_hessian_of_scalar hn hscalar
    f f c c κ hK hr q.property hf hf L L hL hL F₀ σ hF₀ hσ
  exact hdim

/-- Completing the one-dimensional square supplies every scalar shift,
without a separate assertion about the local dimension. -/
theorem NoncollapsedRCD.local_poisson_shifted_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c κ : ℝ) (hK : -κ≤K)
    {p : X} {r : ℝ} (hr : 0<r)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (L : ℝ≥0)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f f)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      ((2:ℝ) • σ.toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic f f))) (b : ℝ) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*r)),
      2*b*c-(n:ℝ)*b^2≤(σ.rnDeriv (hausdorff n X) x).toReal := by
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  filter_upwards [hX.local_poisson_dimensional_density hn hscalar f c κ hK hr
    hf L hL F₀ σ hF₀ hσ] with x hx
  have hp : 0≤(n:ℝ)*((σ.rnDeriv (hausdorff n X) x).toReal-(2*b*c-(n:ℝ)*b^2)) := by
    nlinarith only [hx,sq_nonneg (c-(n:ℝ)*b)]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hn0).mp hp)

end RegularPointCoordinates

end

end OAI
