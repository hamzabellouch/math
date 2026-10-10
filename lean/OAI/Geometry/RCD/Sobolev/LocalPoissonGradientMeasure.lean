import OAI.Geometry.RCD.Sobolev.LocalPoissonMeasureLaplacian
import OAI.Geometry.RCD.Sobolev.LocalGradientBoundedness

namespace OAI

/-! # Full Poisson energy measures from the local gradient alone -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The scalar Bochner measure needs no amplitude assumption on the
Poisson function. Local transport supplies that bound on an interior ball. -/
theorem NoncollapsedRCD.local_poisson_measure_of_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    {p : X} {R b C : ℝ} (hR : 0 < R) (hRb : 3 * R < b)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p b) f c)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 2) C)
    (κ : ℝ) (hK : -κ ≤ K) :
    ∃ (G : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X),
      ∃ hσ : IsFiniteMeasure σ,
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ≤ (L : ℝ) ^ 2) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f f) ∧
      IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) G
        ((2 : ℝ) • @Measure.toSignedMeasure X _ σ hσ -
          (2 * κ) • (hausdorff n X).withDensityᵥ (localGamma (hausdorff n X) hX.quadratic f f)) := by
  let a := (3 * R + b) / 2
  have hab : a < b := by dsimp [a]; linarith
  have hRa : 3 * R < a := by dsimp [a]; linarith
  have hsub : ball p a ⊆ ball p b := ball_subset_ball hab.le
  obtain ⟨A, hA⟩ := hX.local_amplitude_of_gradient hn f L hab hL
  apply hX.local_poisson_measure_laplacian hn measurableSet_ball f c
    (hf.mono _ _ measurableSet_ball hsub) A L
    (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hA)
    (ae_restrict_of_ae_restrict_of_subset hsub hL) hR χ _ κ hK
  simpa only [show 2 * (3 * R / 2) = 3 * R by ring] using
    (closedBall_subset_ball hRa : closedBall p (3 * R) ⊆ ball p a)

/-- The actual scalar Bochner measure exists on every interior ball of a
constant-Laplacian function with locally bounded gradient. All analytic
objects are constructed from the RCD condition. -/
theorem NoncollapsedRCD.local_poisson_energy_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    {p : X} {R b : ℝ} (hR : 0 < R) (hRb : 3 * R < b)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p b) f c)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    (κ : ℝ) (hK : -κ ≤ K) :
    ∃ (G : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X),
      ∃ hσ : IsFiniteMeasure σ,
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ≤ (L : ℝ) ^ 2) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f f) ∧
      IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) G
        ((2 : ℝ) • @Measure.toSignedMeasure X _ σ hσ -
          (2 * κ) • (hausdorff n X).withDensityᵥ (localGamma (hausdorff n X) hX.quadratic f f)) := by
  obtain ⟨C, _, ⟨χ⟩⟩ := hX.goodCutoff_exists hn p (show 0 < 3 * R / 2 by positivity)
  exact hX.local_poisson_measure_of_gradient hn f c hR hRb hf L hL χ κ hK

end RegularPointCoordinates

end

end OAI
