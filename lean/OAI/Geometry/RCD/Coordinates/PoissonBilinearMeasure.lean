import OAI.Geometry.RCD.Sobolev.PoissonScalarFamily
import OAI.Geometry.RCD.Sobolev.FiniteEnergyRepresentatives
import OAI.Geometry.RCD.Sobolev.SignedTestFunctional
import OAI.Geometry.RCD.Coordinates.LocalPositiveBilinearMeasure
import OAI.Geometry.RCD.Sobolev.AnnularLipschitzCutoff

namespace OAI

/-! # One positive measure-valued form for the finite Poisson span

Polarization of the actual scalar measures gives the coefficient measures.
Locality identifies their quadratic tests with each directional scalar
measure. Positivity is then retained on the common interior ball, including
the singular part.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_bilinear_energy_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (κ : ℝ) (hK : -κ ≤ K) (p : X) {r : ℝ} (hr : 0 < r) (L : ℝ≥0)
    (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
      (ball p (8 * r)) (U v) (ell v))
    (hL : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) :
    ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
      ∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v) := by
  classical
  let := hX.separable
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨G, σ, hσ, hGb, hGr, hGt⟩ := hX.poisson_scalar_energy_family hn κ hK p hr L U ell hU hL
  let e (i : Fin (n + 2)) : Euclidean (n + 2) := EuclideanSpace.single i 1
  let H (i j : Fin (n + 2)) := (1 / 2 : ℝ) • (G (e i + e j) - G (e i) - G (e j))
  let s (v : Euclidean (n + 2)) : SignedMeasure X := @Measure.toSignedMeasure X _ (σ v) (hσ v)
  let a (i j : Fin (n + 2)) := (1 / 2 : ℝ) • (s (e i + e j) - s (e i) - s (e j))
  let B := coordinateBilinear H
  let Q := coordinateBilinear a
  have hH (i j : Fin (n + 2)) : SobolevSpace.toLp μ hQ (H i j)
      =ᵐ[μ.restrict (ball p (5 * r / 2))] localGamma μ hQ (U (e i)) (U (e j)) := by
    apply polarized_energy_representative μ hQ _ _ _ _ _ (hGr (e i)) (hGr (e j))
    simpa only [map_add] using hGr (e i + e j)
  have hB (v w : Euclidean (n + 2)) : SobolevSpace.toLp μ hQ (B v w)
      =ᵐ[μ.restrict (ball p (5 * r / 2))] localGamma μ hQ (U v) (U w) :=
    coordinate_energy_representative μ hQ U H hH v w
  have ha (i j : Fin (n + 2)) : a i j = a j i := by
    dsimp only [a]
    rw [add_comm (e i) (e j)]
    congr 1
    abel
  have hentry (i j : Fin (n + 2)) (ψ : SobolevSpace μ hQ) (f : X →ᵇ ℝ)
      (hfc : HasCompactSupport (f : X → ℝ)) (hfs : tsupport f ⊆ ball p (5 * r / 2))
      (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] f) :
      signedTestIntegral f (a i j) = bochnerTestForm μ hQ κ (H i j) ψ := by
    have ht (v : Euclidean (n + 2)) : signedTestIntegral f (s v) =
        bochnerTestForm μ hQ κ (G v) ψ := by
      have : IsFiniteMeasure (σ v) := hσ v
      change (∫ᵛ x, f x ∂<•(σ v).toSignedMeasure) = _
      rw [VectorMeasure.integral_toSignedMeasure]
      exact (hGt v ψ f f.continuous hfc hfs hψ).symm
    change signedTestIntegral f ((1 / 2 : ℝ) • (s (e i + e j) - s (e i) - s (e j))) = _
    simp only [map_smul, map_sub, ht, H, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  have htest (v : Euclidean (n + 2)) (ψ : SobolevSpace μ hQ) (f : X →ᵇ ℝ)
      (hfc : HasCompactSupport (f : X → ℝ)) (hfs : tsupport f ⊆ ball p (5 * r / 2))
      (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] f) :
      signedTestIntegral f (Q v v) = bochnerTestForm μ hQ κ (G v) ψ := by
    have he : signedTestIntegral f (Q v v) = bochnerTestForm μ hQ κ (B v v) ψ := by
      rw [signedTestIntegral_coordinate]
      simp_rw [hentry _ _ ψ f hfc hfs hψ]
      change _ = bochnerTestForm μ hQ κ (coordinateBilinear H v v) ψ
      rw [coordinateBilinear_apply]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact he.trans (bochnerTestForm_congr_on μ hQ measurableSet_ball κ
      ((hB v v).trans (hGr v).symm) ψ f hψ hfs)
  have hpos (v : Euclidean (n + 2)) (f : compactLipschitzTests (ball p (5 * r / 2)))
      (hf : 0 ≤ (f : X →ᵇ ℝ)) : 0 ≤ ∫ᵛ x, (f : X →ᵇ ℝ) x ∂<•(Q v v) := by
    let ψ := compactTestSobolev μ hQ _ f
    have hψ := compactTestSobolev_coe μ hQ _ f
    change 0 ≤ signedTestIntegral (f : X →ᵇ ℝ) (Q v v)
    rw [htest v ψ f f.property.choose_spec.2.1 f.property.choose_spec.2.2 hψ,
      hGt v ψ f (f : X →ᵇ ℝ).continuous f.property.choose_spec.2.1 f.property.choose_spec.2.2 hψ]
    exact integral_nonneg hf
  obtain ⟨χ, C, hχ, hχc, hχs, hχb, hχ1⟩ :=
    exists_annular_lipschitz_cutoff p (a := 2 * r) (b := 9 * r / 4) (by linarith)
  let M := positiveBilinearMeasure_of_local_tests Q
    (coordinateBilinear_symmetric a ha) measurableSet_closedBall χ hχ hχc
    (hχs.trans (closedBall_subset_ball (show 9 * r / 4 < 5 * r / 2 by linarith)))
    (fun x => (hχb x).1) hχ1 hpos
  refine ⟨M, ?_⟩
  intro v
  have hsmall : ball p (2 * r) ⊆ ball p (5 * r / 2) := ball_subset_ball (by linarith)
  have hrep := ae_restrict_of_ae_restrict_of_subset hsmall (hGr v)
  refine ⟨{ energy := G v, representative := hrep, bounded := ?_, measure_laplacian := ?_ }⟩
  · filter_upwards [hGb v] with x hx
    rw [abs_of_nonneg hx.1]
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using hx.2
  · have hid (ψ : SobolevSpace μ hQ) (f : X → ℝ) (hfc : Continuous f)
        (hfs : HasCompactSupport f) (hfsub : tsupport f ⊆ ball p (2 * r))
        (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] f) :
        (∫ x, f x ∂M.measure v) = bochnerTestForm μ hQ κ (G v) ψ := by
      let w : X →ᵇ ℝ := ofCompactSupport f hfc hfs
      rw [← VectorMeasure.integral_toSignedMeasure, M.measure_toSignedMeasure]
      change signedTestIntegral w ((Q v v).restrict (closedBall p (2 * r))) = _
      rw [signedTestIntegral_restrict w _ measurableSet_closedBall
        (hfsub.trans ball_subset_closedBall)]
      exact htest v ψ w hfs (hfsub.trans hsmall) hψ
    have hlap := bochner_measure_laplacian μ hQ measurableSet_ball (U v) (G v) κ (M.measure v) hrep hid
    simpa only [harmonicBochnerSource, M.measure_toSignedMeasure] using hlap

end RegularPointCoordinates

end

end OAI
