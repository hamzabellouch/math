import OAI.Geometry.RCD.Harmonic.CanonicalRadialSize
import OAI.Geometry.RCD.Harmonic.AffineCenterBounds

namespace OAI

/-! # Center values of the actual least-squares radial fits -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published harmonic mean-value input bounds the center value of
every actual radial fit by radius times the current covector norm.
The same evaluation constant works for all source scales and centers. -/
theorem canonical_radial_affine_center_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {κ r0 B J C ε : ℝ} {p : X}
      (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
      (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
      (i : ℕ) (r : ℝ), 0 < r → r ≤ 4 * distanceSourceRadius r0 i → -κ₀ ≤ K * r ^ 2 → 0 ≤ ε →
    ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) (u j)) →
      ContinuousOn v (ball p r) →
      (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
        (hausdorff n X).restrict (ball p r)] fun x => v x j) →
    ∀ F : Euclidean n ≃L[ℝ] Euclidean n,
      (∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
        localGamma (hausdorff n X) hX.quadratic
          (transformedColumn (hausdorff n X) hX.quadratic u F j)
          (transformedColumn (hausdorff n X) hX.quadratic u F j) x ≤ (1 + ε) ^ 2) →
    ∀ (b : Euclidean n) {H : ℝ}
      (ha : ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
        localGamma (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u b)
          (sobolevColumnMap (hausdorff n X) hX.quadratic u b) x ≤ H),
      let μ := hausdorff n X
      let hfin := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
      let f := radialPairingLp μ hX.quadratic (ball p r) (T.distanceDatum μ hX.quadratic i)
        (sobolevColumnMap μ hX.quadratic u b) ha
      ∃ c : ℝ, ∃ a : Euclidean n,
        affineProjection μ hX.quadratic u (ball p r) hfin f =
          affineCoordinateMap μ hX.quadratic u (ball p r) hfin (c, a) ∧
        |c + ⟪v p, a⟫_ℝ| ≤ M * r * ((n : ℝ) * (1 + ε)) * ‖F.symm b‖ := by
  obtain ⟨M, hM, heval⟩ := affine_evaluation_of_mean_value hX hmean hn hκ₀
  refine ⟨M, hM, ?_⟩
  intro κ r0 B J C ε p S T i r hr hrr hcurv hε u v hu hv hrep F hgrad b H ha
  dsimp only
  let μ := hausdorff n X
  let hfin := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
  let f := radialPairingLp μ hX.quadratic (ball p r) (T.distanceDatum μ hX.quadratic i)
    (sobolevColumnMap μ hX.quadratic u b) ha
  have hη : SobolevSpace.toLp μ hX.quadratic (T.cutoff i).sobolev =ᵐ[μ.restrict (ball p r)]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (T.cutoff i).representative,
      ae_restrict_mem measurableSet_ball] with x hx hxr
    exact hx.trans ((T.cutoff i).one x ((ball_subset_ball hrr) hxr))
  obtain ⟨c, a, hfit⟩ := affineProjection_has_coefficients μ hX.quadratic u (ball p r) hfin f
  refine ⟨c, a, hfit, ?_⟩
  have hb := affineFit_center_bound μ hX.quadratic u (ball p r) hfin (v p)
    (zero_le_one.trans hM) (heval p r hr hcurv u v hu hv hrep (T.cutoff i).sobolev hη) f c a hfit
  have hs := T.radialPairing_size μ hX.quadratic i hr.le hrr hfin
    (ne_of_gt (hX.fullSupport p r hr)) hε u F hgrad b ha
  exact hb.trans ((mul_le_mul_of_nonneg_left hs (zero_le_one.trans hM)).trans_eq (by ring))

end RegularPointCoordinates

end

end OAI
