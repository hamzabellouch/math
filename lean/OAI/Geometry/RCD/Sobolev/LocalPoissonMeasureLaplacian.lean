import OAI.Geometry.RCD.Sobolev.LocalPoissonFullBochnerMeasure
import OAI.Geometry.RCD.Sobolev.BochnerMeasureIdentity
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # Actual full measure Laplacians of local Poisson energy densities -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_measure_laplacian {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (A L : ℝ≥0) (hA : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    {p : X} {R C : ℝ} (hR : 0 < R)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 2) C)
    (hsub : closedBall p (2 * (3 * R / 2)) ⊆ Ω)
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
  let μ := hausdorff n X
  obtain ⟨g, hg, hgA, hfg⟩ := hf.bounded_extension μ hX.quadratic hΩ A hA
  have hΓ := localGamma_pair_congr_ae μ hX.quadratic hfg hfg
  have hgL : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hX.quadratic g g x ≤ (L : ℝ) ^ 2 := by
    filter_upwards [hΓ, hL] with x hx hbound
    rw [← hx]
    exact hbound
  obtain ⟨G, σ, hσ, hGb, hGr, hrep⟩ :=
    hX.local_poisson_full_bochner_measure hn hΩ g c hg A L hgA hgL hR χ hsub κ hK
  have hsmall : ball p R ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  have hGf : SobolevSpace.toLp μ hX.quadratic G =ᵐ[μ.restrict (ball p R)]
      localGamma μ hX.quadratic f f :=
    hGr.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsmall hΓ))
  have : IsFiniteMeasure σ := hσ
  exact ⟨G, σ, hσ, hGb, hGf,
    bochner_measure_laplacian μ hX.quadratic measurableSet_ball f G κ σ hGf hrep⟩

/-- At bounded rescaled curvature the cutoff is constructed from the RCD
heat resolvent; only local bounds on the Poisson function are needed. -/
theorem NoncollapsedRCD.local_poisson_measure_laplacian_of_curvature {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (A L : ℝ≥0) (hA : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    {p : X} {R : ℝ} (hR : 0 < R) (hsub : closedBall p (3 * R) ⊆ Ω)
    (hcurv : -1 ≤ K * (3 * R / 2) ^ 2) (κ : ℝ) (hK : -κ ≤ K) :
    ∃ (G : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X),
      ∃ hσ : IsFiniteMeasure σ,
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ≤ (L : ℝ) ^ 2) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f f) ∧
      IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) G
        ((2 : ℝ) • @Measure.toSignedMeasure X _ σ hσ -
          (2 * κ) • (hausdorff n X).withDensityᵥ (localGamma (hausdorff n X) hX.quadratic f f)) := by
  obtain ⟨C, _, hcutoff⟩ := hX.goodCutoffInput hn
  obtain ⟨χ⟩ := hcutoff p (3 * R / 2) (by positivity) hcurv
  apply hX.local_poisson_measure_laplacian hn hΩ f c hf A L hA hL hR χ _ κ hK
  simpa only [show 2 * (3 * R / 2) = 3 * R by ring] using hsub

end RegularPointCoordinates

end

end OAI
