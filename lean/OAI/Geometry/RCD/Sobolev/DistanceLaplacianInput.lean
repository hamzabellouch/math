import OAI.Geometry.RCD.Sobolev.PositiveDistancePoisson
import OAI.Geometry.RCD.Harmonic.RadialSquaredDistance

namespace OAI

/-! # The exact distance-Laplacian input

Gigli, *On the differential structure of metric measure spaces and
applications*, Mem. AMS 236 (2015), Corollary 5.15, equation (5.29), and
Theorem 5.3, give the local distance eikonal identity and the positive
Laplacian defect. The elementary hyperbolic comparison bounds the density
by n + kappa R² on B_R when Ricci is bounded below by -kappa.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def LocalSquaredDistanceInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  letI : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  2 ≤ n → ∀ κ : ℝ, 0 ≤ κ → -κ ≤ K → ∀ (p : X) (R : ℝ) (hR : 0 < R),
    ∃ σ : Measure X, ∃ _hσ : IsFiniteMeasure σ,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
        localGamma (hausdorff n X) hX.quadratic (inwardSobolev (hausdorff n X) hX.quadratic p R)
          (inwardSobolev (hausdorff n X) hX.quadratic p R) x = 1) ∧
      ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (L : ℝ≥0),
        LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p R →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        energyForm (hausdorff n X) hX.quadratic
          (inwardQuadratic (hausdorff n X) hX.quadratic p hR.le) ψ +
          ((n : ℝ) + κ * R ^ 2) * (∫ x, v x ∂hausdorff n X) = ∫ x, v x ∂σ

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Adding the cutoff constant leaves the source unchanged on the
working ball, and compact support turns the global integral into its
required local form. -/
theorem positiveSquaredDistance_source {p : X} {r R C a : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C) (hrR : r ≤ R) (σ : Measure X)
    (hsource : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p R →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ (inwardQuadratic μ hQ p hR) ψ + a * (∫ x, v x ∂μ) = ∫ x, v x ∂σ) :
    ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p r →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ (positiveSquaredDistance μ hQ hR χ) ψ +
        a * (∫ x in ball p r, v x ∂μ) = ∫ x, v x ∂σ := by
  intro ψ v L hv hc hs hψ
  have hmem : ψ ∈ SobolevSpace.dirichlet μ hQ (ball p R) :=
    (SobolevSpace.dirichletCore μ hQ (ball p R)).le_topologicalClosure
      ⟨v, L, hv, hc, hs.trans (ball_subset_ball hrR), hψ⟩
  have hzero := (χ.harmonic_on_inner_ball μ hQ) ψ hmem
  have hi : (∫ x in ball p r, v x ∂μ) = ∫ x, v x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Filter.Eventually.of_forall fun x hx => by
      by_contra hn
      exact hx (hs (subset_tsupport v hn))
  rw [positiveSquaredDistance, energyForm_add_left, energyForm_smul_left, hzero, mul_zero,
    add_zero, hi]
  exact hsource ψ v L hv hc (hs.trans (ball_subset_ball hrR)) hψ

end RegularPointCoordinates

end

end OAI
