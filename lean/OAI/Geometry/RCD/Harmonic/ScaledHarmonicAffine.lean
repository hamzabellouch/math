import OAI.Geometry.RCD.Harmonic.HarmonicAffineNondegeneracy

namespace OAI

/-! # Radius-weighted affine coefficients in centered harmonic coordinates -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Weighting the exact-frame coefficient by the physical radius gives
one affine nondegeneracy constant at every positive scale. The constant
coefficient retains its unweighted normalization. -/
theorem scaled_harmonic_affine_nondegeneracy {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hgradient : LocalHarmonicL2GradientInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Cg Cm : ℝ, 1 ≤ Cg ∧ 1 ≤ Cm ∧
      ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (V : X → Euclidean n),
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) (u j)) →
      ContinuousOn V (ball p R) → V p = 0 →
      (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun x => V x j) →
      ∀ (N : Euclidean n ≃L[ℝ] Euclidean n),
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u)
        (ball p (R / 2)) measurableSet_ball N →
      ∀ η : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun _ => (1 : ℝ)) →
      ∀ (c : ℝ) (a : Euclidean n),
      |c| + R * ‖N.symm a‖ ≤ (Cm + Cg) *
        ‖normalizeLocalL2 (hausdorff n X) (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p R)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
  obtain ⟨Cg, hCg, hcoeff⟩ := hgradient.affine_coefficient hn hκ
  obtain ⟨Cm, hCm, heval⟩ := affine_evaluation_of_mean_value hX hmean hn hκ
  refine ⟨Cg, Cm, hCg, hCm, ?_⟩
  intro p R hR hcurv u V hu hV hVp hrep N hN η hη c a
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let w := c • η + sobolevColumnMap μ hQ u a
  have hηharm := isSobolevHarmonicOn_of_local_constant μ hQ (ball p R) measurableSet_ball η 1 hη
  have hw : IsSobolevHarmonicOn μ hQ (ball p R) w :=
    (hηharm.smul μ hQ c).add μ hQ (IsSobolevHarmonicOn.linearCombination μ hQ hu a)
  have hdiff : SobolevSpace.toLp μ hQ (w - sobolevColumnMap μ hQ u a) =ᵐ[
      μ.restrict (ball p R)] fun _ => c := by
    simp only [w, add_sub_cancel_right, map_smul]
    filter_upwards [hη, ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp μ hQ η))]
      with x hx hc
    simp only [hc, Pi.smul_apply, smul_eq_mul]
    change c * SobolevSpace.toLp (hausdorff n X) hX.quadratic η x = c
    rw [hx, mul_one]
  have hrest : SobolevSpace.restrictLp μ hQ (ball p R) w =
      affineCoordinateMap μ hQ u (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a) := by
    rw [affineCoordinateMap_apply]
    dsimp only [w]
    rw [map_add, map_smul, restrictLp_eq_one_of_representative μ hQ η _ _ hη]
  have hc := hcoeff p R hR hcurv u N hN a w c hw hdiff
  rw [hrest] at hc
  have hv := heval p R hR hcurv u V hu hV hrep η hη c a
  rw [hVp, inner_zero_left, add_zero] at hv
  have hlin : ‖N.symm a‖ ≤ Cg / R *
      ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap μ hQ u (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg (by linarith) hR.le) (norm_nonneg _))).mp
    simpa only [mul_pow] using hc
  have hweighted := mul_le_mul_of_nonneg_left hlin hR.le
  have heq : R * (Cg / R *
      ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap μ hQ u (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖) =
      Cg * ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap μ hQ u (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
    field_simp
  rw [heq] at hweighted
  nlinarith only [hv, hweighted]

end RegularPointCoordinates

end

end OAI
