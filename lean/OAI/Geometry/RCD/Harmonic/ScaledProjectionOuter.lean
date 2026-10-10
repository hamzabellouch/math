import OAI.Geometry.RCD.Harmonic.GeometricProjectionOuter
import OAI.Geometry.RCD.Harmonic.RescaledRadialFunction

namespace OAI

/-! # Uniform outer control after the physical projection rescaling -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The physical projection and forcing both have size `r²`. Dividing
both by that factor gives the same uniform transport and coefficient bounds;
the radial error retains its natural length scale. -/
theorem LocalHarmonicL2GradientInput.scaled_projected_residual_outer
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ H V W B J E D : ℝ} (hκ : 0 ≤ κ) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hE : 0 ≤ E) (Cw : ℝ≥0) :
    ∃ G T : ℝ, 0 ≤ G ∧ 0 ≤ T ∧
      ∀ (p : X) (R a r : ℝ), 0 < R → 0 ≤ a → a ≤ (n : ℝ) + 1 → -κ ≤ K * R ^ 2 → 0 < r →
      ∀ (f w η e : SobolevSpace (hausdorff n X) hX.quadratic)
        (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n) (ell : Euclidean n) (k σ : ℝ), 0 ≤ σ →
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (4 * R)) f a →
      ∀ hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * R)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ (B * R) ^ 2,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * R)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ (Cw : ℝ) * r ^ 2) →
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
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R)) e)‖ ≤ E * r ^ 2 * σ →
      (∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball p (4 * R))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R))
          (sobolevColumnMap (hausdorff n X) hX.quadratic u b))‖ ≤ J * (R * ‖N.symm b‖)) →
      ∀ g : X → ℝ, MemLp g 2 (hausdorff n X) →
      localGamma (hausdorff n X) hX.quadratic f
        (inwardSobolev (hausdorff n X) hX.quadratic p (3 * R)) =ᵐ[
          (hausdorff n X).restrict (ball p (3 * R))] (fun x => g x - dist p x) →
      (hausdorff n X) (sphere p R) = 0 →
      (∫ x in ball p (4 * R), (g x) ^ 2 ∂hausdorff n X) ≤
        D ^ 2 * R ^ 2 * (hausdorff n X).real (ball p R) * σ ^ 2 →
      |(r ^ 2)⁻¹ * k| + R * ‖N.symm ((r ^ 2)⁻¹ • ell)‖ ≤ G *
          (‖normalizeLocalL2 (hausdorff n X) (ball p R)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) ((r ^ 2)⁻¹ • w))‖ + σ) ∧
      ‖normalizeLocalL2 (hausdorff n X) (ball p (2 * R))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (2 * R)) ((r ^ 2)⁻¹ • w))‖ ≤ T *
          (‖normalizeLocalL2 (hausdorff n X) (ball p R)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) ((r ^ 2)⁻¹ • w))‖ + σ) := by
  obtain ⟨G, T, hG, hT, hb⟩ := hinput.projected_residual_outer hn hκ hH hV hW hB hJ hE Cw
  refine ⟨G, T, hG, hT, ?_⟩
  intro p R a r hR ha han hcurv hr f w η e u N ell k σ hσ hlap hf hw hwharm hη hpos
    hhalf hvol hbound heuler he hU g hg hradial hsphere herror
  let c := (r ^ 2)⁻¹
  have hc : 0 < c := inv_pos.mpr (sq_pos_of_pos hr)
  have hscaledw : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * R)),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (c • w) x| ≤ Cw :=
    rescaled_radial_value (hausdorff n X) hX.quadratic _ w hr hw
  have he' : ‖normalizeLocalL2 (hausdorff n X) (ball p (4 * R))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R)) (c • e))‖ ≤ E * σ := by
    rw [map_smul, normalizeLocalL2_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc
      _ ≤ c * (E * r ^ 2 * σ) := mul_le_mul_of_nonneg_left he hc.le
      _ = E * σ := by dsimp only [c]; field_simp
  have hid : localRadialDerivative (hausdorff n X) hX.quadratic (ball p (4 * R)) f hf (c • w) =
      SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (4 * R))
        (c • w + sobolevColumnMap (hausdorff n X) hX.quadratic u (c • ell) +
          (c * k) • η + c • e) := by
    rw [map_smul, heuler, ← map_smul]
    congr 1
    rw [map_smul]
    module
  exact hb p R a hR ha han hcurv f (c • w) η (c • e) u N (c • ell) (c * k) σ hσ
    hlap hf hscaledw (hwharm.smul _ _ c) hη hpos hhalf hvol hbound hid he'
    (hU (c • ell)) g hg hradial hsphere herror

end RegularPointCoordinates

end

end OAI
