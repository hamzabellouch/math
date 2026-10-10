import OAI.Geometry.RCD.Sobolev.LocalPoissonEnergyDensity
import OAI.Geometry.RCD.Sobolev.PositiveSobolevTestMeasure
import OAI.Geometry.RCD.Sobolev.SobolevTestFunctional

namespace OAI

/-! # Full continuous-test Bochner measures for local Poisson data

The three-halves interior ratio leaves room for the good cutoff inside
an eightfold working ball. The identity holds on every continuous
compactly supported Sobolev test
and retains all of the positive measure.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_full_bochner_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (A L : ℝ≥0) (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    {p : X} {R C : ℝ} (hR : 0 < R)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 2) C)
    (hsub : closedBall p (2 * (3 * R / 2)) ⊆ Ω)
    (κ : ℝ) (hK : -κ ≤ K) :
    ∃ (G : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X),
      IsFiniteMeasure σ ∧
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ≤ (L : ℝ) ^ 2) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f f) ∧
      ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p R →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        (∫ x, v x ∂σ) = -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G ψ +
          κ * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) := by
  let := hX.separable
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨G, hGb, hGr, hpos⟩ := hX.local_poisson_energy_density_continuous_tests hn hΩ f c hf A L hA hL
    (show 0 < 3 * R / 2 by positivity) χ hsub
  let T := compactSobolevTestLift μ hX.quadratic (ball p (3 * R / 2))
  let Φ := (sobolevSourceFunctional μ hX.quadratic ((-(1 / 2 : ℝ)) • G)
    (κ • SobolevSpace.toLp μ hX.quadratic G)).comp T
  have hformula (b : compactSobolevTests μ hX.quadratic (ball p (3 * R / 2))) : Φ b =
      -(1 / 2 : ℝ) * energyForm μ hX.quadratic G (T b) +
      κ * inner ℝ (SobolevSpace.toLp μ hX.quadratic (T b)) (SobolevSpace.toLp μ hX.quadratic G) := by
    change energyForm μ hX.quadratic ((-(1 / 2 : ℝ)) • G) (T b) +
      inner ℝ (κ • SobolevSpace.toLp μ hX.quadratic G) (SobolevSpace.toLp μ hX.quadratic (T b)) = _
    rw [energyForm_smul_left, real_inner_smul_left, real_inner_comm]
  have hΦ (b : compactSobolevTests μ hX.quadratic (ball p (3 * R / 2))) (hb : 0 ≤ (b : X →ᵇ ℝ)) : 0 ≤ Φ b := by
    obtain ⟨hbc, hbs, _⟩ := b.property
    have hrep := compactSobolevTestLift_coe μ hX.quadratic (ball p (3 * R / 2)) b
    have h := hpos (T b) (b : X →ᵇ ℝ) (b : X →ᵇ ℝ).continuous hbc hbs hrep (fun x => hb x)
    have hi : 0 ≤ inner ℝ (SobolevSpace.toLp μ hX.quadratic (T b)) (SobolevSpace.toLp μ hX.quadratic G) := by
      rw [L2.inner_def]
      apply integral_nonneg_of_ae
      filter_upwards [hGb, hrep] with x hx hy
      change SobolevSpace.toLp μ hX.quadratic (T b) x = (b : X →ᵇ ℝ) x at hy
      simp only [Real.inner_apply, hy]
      exact mul_nonneg (hb x) hx.1
    rw [hformula]
    have hc : 0 ≤ (κ + K) * inner ℝ (SobolevSpace.toLp μ hX.quadratic (T b))
        (SobolevSpace.toLp μ hX.quadratic G) := mul_nonneg (by linarith) hi
    linarith
  obtain ⟨σ, hσ, hσrep⟩ := exists_positive_sobolev_test_measure μ hX.quadratic p hR Φ hΦ
  refine ⟨G, σ, hσ, hGb,
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hGr, ?_⟩
  intro ψ v hv hvc hvs hψ
  let cv : C_c(X, ℝ) := ⟨⟨v, hv⟩, hvc⟩
  let b : compactSobolevTests μ hX.quadratic (ball p R) := ⟨cv.toBoundedContinuousFunction, hvc, hvs, ψ, hψ⟩
  let b' : compactSobolevTests μ hX.quadratic (ball p (3 * R / 2)) :=
    ⟨cv.toBoundedContinuousFunction, hvc, hvs.trans (ball_subset_ball (by linarith)), ψ, hψ⟩
  have heq : T b' = ψ := by
    apply Subtype.ext
    apply Lp.ext
    exact (compactSobolevTestLift_coe μ hX.quadratic _ b').trans hψ.symm
  have hh := hσrep b
  change (∫ x, v x ∂σ) = Φ b' at hh
  rw [hformula, heq] at hh
  exact hh

end RegularPointCoordinates

end

end OAI
