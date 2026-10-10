import OAI.Geometry.RCD.Coordinates.NormalizedResidualOuter
import OAI.Geometry.RCD.Harmonic.ScaledForcingCoefficient

namespace OAI

/-! # Uniform outer control for the actual projected Euler equation -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The local harmonic estimate controls the affine forcing from the
inner residual. The radial transport estimate then controls its outer
norm, with both constants preceding all centers and radii. -/
theorem LocalHarmonicL2GradientInput.projected_residual_outer
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ H V W B J E D : ℝ} (hκ : 0 ≤ κ) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hE : 0 ≤ E) (Cw : ℝ≥0) :
    ∃ G T : ℝ, 0 ≤ G ∧ 0 ≤ T ∧
      ∀ (p : X) (R a : ℝ), 0 < R → 0 ≤ a → a ≤ (n : ℝ) + 1 → -κ ≤ K * R ^ 2 →
      ∀ (f w η e : SobolevSpace (hausdorff n X) hX.quadratic)
        (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n) (ell : Euclidean n) (k σ : ℝ), 0 ≤ σ →
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (4 * R)) f a →
      ∀ hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * R)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ (B * R) ^ 2,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * R)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ Cw) →
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p (4 * R))] fun _ => (1 : ℝ)) →
      0 < (hausdorff n X).real (ball p R) →
      (hausdorff n X).real (ball p R) ≤ V ^ 2 * (hausdorff n X).real (ball p (R / 2)) →
      (hausdorff n X).real (ball p (4 * R)) ≤ W ^ 2 * (hausdorff n X).real (ball p R) →
      (∀ c v, |c| + R * ‖N.symm v‖ ≤ H *
        ‖normalizeLocalL2 (hausdorff n X) (ball p (R / 2))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p (R / 2))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, v))‖) →
      (localRadialDerivative (hausdorff n X) hX.quadratic (ball p (4 * R)) f hf w =
        SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R))
          (w + sobolevColumnMap (hausdorff n X) hX.quadratic u ell + k • η + e)) →
      ‖normalizeLocalL2 (hausdorff n X) (ball p (4 * R))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R)) e)‖ ≤ E * σ →
      ‖normalizeLocalL2 (hausdorff n X) (ball p (4 * R))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R))
          (sobolevColumnMap (hausdorff n X) hX.quadratic u ell))‖ ≤ J * (R * ‖N.symm ell‖) →
      ∀ g : X → ℝ, MemLp g 2 (hausdorff n X) →
      localGamma (hausdorff n X) hX.quadratic f
        (inwardSobolev (hausdorff n X) hX.quadratic p (3 * R)) =ᵐ[
          (hausdorff n X).restrict (ball p (3 * R))] (fun x => g x - dist p x) →
      (hausdorff n X) (sphere p R) = 0 →
      (∫ x in ball p (4 * R), (g x) ^ 2 ∂hausdorff n X) ≤
        D ^ 2 * R ^ 2 * (hausdorff n X).real (ball p R) * σ ^ 2 →
      |k| + R * ‖N.symm ell‖ ≤ G *
          (‖normalizeLocalL2 (hausdorff n X) (ball p R)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ + σ) ∧
      ‖normalizeLocalL2 (hausdorff n X) (ball p (2 * R))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (2 * R)) w)‖ ≤ T *
          (‖normalizeLocalL2 (hausdorff n X) (ball p R)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ + σ) := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨C, hC, hc⟩ := hinput.scaled_forcing_coefficients hn hκ
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  let G := H * (B * C + V + V * W * E)
  let F := (1 + J) * G + E
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  obtain ⟨T, hT, ht⟩ := normalized_residual_outer_bound μ hQ n (E := D) hF hW Cw
  refine ⟨G, T, hG, hT, ?_⟩
  intro p R a hR ha han hcurv f w η e u N ell k σ hσ hlap hf hw hwharm hη hpos hhalf hvol hbound heuler he hU g hg hradial hsphere herror
  let α := ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp μ hQ (ball p R) w)‖
  let U := sobolevColumnMap μ hQ u
  let q := U ell + k • η + e
  have hsub : ball p (R / 2) ⊆ ball p (4 * R) := ball_subset_ball (by linarith)
  have hsubR : ball p R ⊆ ball p (4 * R) := ball_subset_ball (by linarith)
  have hfsmall := ae_restrict_of_ae_restrict_of_subset hsub hf
  have heulersmall : localRadialDerivative μ hQ (ball p (R / 2)) f hfsmall w =
      SobolevSpace.restrictLp μ hQ (ball p (R / 2)) (w + U ell + k • η + e) := by
    apply localRadialDerivative_eq_restrict
    have hgamma := localRadialDerivative_representative μ hQ (ball p (4 * R)) f w hf
    rw [heuler] at hgamma
    exact ae_restrict_of_ae_restrict_of_subset hsub
      ((SobolevSpace.restrictLp_coe μ hQ _ _).symm.trans hgamma)
  have hposlarge : 0 < μ.real (ball p (4 * R)) := hpos.trans_le
    (measureReal_mono hsubR (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)))
  have heR := normalized_fit_restrict_norm μ hQ hsubR
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hposlarge hpos e hW
    (mul_nonneg hE hσ) hvol he
  have hcoeff := hc p R hR hcurv f w η e (B * R) (mul_nonneg hB hR.le)
    hfsmall hwharm (ae_restrict_of_ae_restrict_of_subset hsub hη) u N ell k H V
    (W * (E * σ)) hH hV (by positivity) hhalf hbound heulersmall heR
  have hcoeff' : |k| + R * ‖N.symm ell‖ ≤ G * (α + σ) := by
    have hcancel : B * R * C / R = B * C := by field_simp
    rw [hcancel] at hcoeff
    change |k| + R * ‖N.symm ell‖ ≤ H * ((B * C + V) * α + V * (W * (E * σ))) at hcoeff
    have hα : 0 ≤ α := norm_nonneg _
    have hinner : (B * C + V) * α + V * (W * (E * σ)) ≤
        (B * C + V + V * W * E) * (α + σ) := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hV hW) hE) hα,
        mul_nonneg (add_nonneg (mul_nonneg hB hC0) hV) hσ]
    calc
      _ ≤ H * ((B * C + V + V * W * E) * (α + σ)) :=
        hcoeff.trans (mul_le_mul_of_nonneg_left hinner hH)
      _ = G * (α + σ) := by dsimp only [G]; ring
  have hforce := weighted_affine_forcing_norm_bound μ hQ (ball p (4 * R))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_gt (hX.fullSupport p (4 * R) (by positivity))) η e hη U N ell k
    hR.le hJ hE (norm_nonneg _) hU hcoeff' he
  have heuler' : localRadialDerivative μ hQ (ball p (4 * R)) f hf w =
      SobolevSpace.restrictLp μ hQ (ball p (4 * R)) (w + q) := by
    rw [heuler]
    congr 1
    dsimp only [q, U]
    module
  exact ⟨hcoeff', ht R a hR ha han p f w q σ hσ hlap hf hw g hg heuler'
    hradial hsphere (fun _ => ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hpos hvol hforce herror⟩

end RegularPointCoordinates

end

end OAI
