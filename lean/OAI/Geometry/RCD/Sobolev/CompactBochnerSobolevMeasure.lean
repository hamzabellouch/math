import OAI.Geometry.RCD.Sobolev.CompactBochnerTest
import OAI.Geometry.RCD.Sobolev.BochnerSourceFunctionals
import OAI.Geometry.RCD.Sobolev.PositiveSobolevTestMeasure

namespace OAI

/-! # The full Bochner measure on continuous Sobolev tests

Positivity on continuous compact Sobolev tests gives a finite measure on each
interior ball. The formula retains the square of the L² Laplacian and the
gradient pairing, and hence needs no derivative of that Laplacian.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_bochner_sobolev_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u) {R : ℝ} (hR : 0 < R) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧
      ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p R →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        (∫ x, v x ∂σ) =
          -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G ψ -
          K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) +
          (∫ x, v x * (d x) ^ 2 ∂hausdorff n X) +
          weightedGamma (hausdorff n X) hX.quadratic d u ψ := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  have huL := SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic u hφ hu
  let H := SobolevSpace.toLp μ hX.quadratic G
  let q := (-(1 / 2 : ℝ)) • G
  let ρ := (-K) • H
  let T := compactSobolevTestLift μ hX.quadratic (ball p (3 * R / 2))
  let J := (boundedIntegralFunctional μ (fun x => (d x) ^ 2) (Lp.memLp d).integrable_sq).comp
    (compactSobolevTests μ hX.quadratic (ball p (3 * R / 2))).subtype
  let Φ := (sobolevSourceFunctional μ hX.quadratic q ρ).comp T + J +
    (gammaSourceFunctional μ hX.quadratic d u L huL).comp T
  have hformula (b : compactSobolevTests μ hX.quadratic (ball p (3 * R / 2))) : Φ b =
      -(1 / 2 : ℝ) * energyForm μ hX.quadratic G (T b) -
      K * inner ℝ (SobolevSpace.toLp μ hX.quadratic (T b)) H +
      (∫ x, (b : X →ᵇ ℝ) x * (d x) ^ 2 ∂μ) + weightedGamma μ hX.quadratic d u (T b) := by
    change energyForm μ hX.quadratic ((-(1 / 2 : ℝ)) • G) (T b) +
      inner ℝ ((-K) • H) (SobolevSpace.toLp μ hX.quadratic (T b)) +
      (∫ x, (b : X →ᵇ ℝ) x * (d x) ^ 2 ∂μ) + weightedGamma μ hX.quadratic d u (T b) = _
    rw [energyForm_smul_left, real_inner_smul_left, real_inner_comm H]
    ring
  have hΦ (b : compactSobolevTests μ hX.quadratic (ball p (3 * R / 2))) (hb : 0 ≤ (b : X →ᵇ ℝ)) :
      0 ≤ Φ b := by
    rw [hformula]
    exact hX.compact_bochner_sobolev_test hn hφ hs p u hu d hd G hG (T b) (b : X →ᵇ ℝ).continuous.measurable
      (compactSobolevTestLift_coe μ hX.quadratic _ b) ‖(b : X →ᵇ ℝ)‖₊
      (fun x => (b : X →ᵇ ℝ).norm_coe_le_norm x) (fun x => hb x)
  obtain ⟨σ, hσ, hσrep⟩ := exists_positive_sobolev_test_measure μ hX.quadratic p hR Φ hΦ
  refine ⟨σ, hσ, ?_⟩
  intro ψ v hv hvc hsup hrep
  let cv : C_c(X, ℝ) := ⟨⟨v, hv⟩, hvc⟩
  let b : compactSobolevTests μ hX.quadratic (ball p R) := ⟨cv.toBoundedContinuousFunction, hvc, hsup, ψ, hrep⟩
  let b' : compactSobolevTests μ hX.quadratic (ball p (3 * R / 2)) :=
    ⟨cv.toBoundedContinuousFunction, hvc, hsup.trans (ball_subset_ball (by linarith)), ψ, hrep⟩
  have heq : T b' = ψ := by
    apply Subtype.ext
    apply Lp.ext
    exact (compactSobolevTestLift_coe μ hX.quadratic _ b').trans hrep.symm
  have hh := hσrep b
  change (∫ x, v x ∂σ) = Φ b' at hh
  rw [hformula, heq] at hh
  exact hh

end RegularPointCoordinates

end

end OAI
