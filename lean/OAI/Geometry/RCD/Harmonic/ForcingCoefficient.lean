import OAI.Geometry.RCD.Sobolev.ProjectedEulerIdentity
import OAI.Geometry.RCD.Harmonic.HarmonicRadialBound
import OAI.Geometry.RCD.Coordinates.RadialFitRestriction

namespace OAI

/-! # Small forcing coefficients from the harmonic residual -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [BorelSpace X] [ProperSpace X] in
theorem normalized_fit_restrict_norm (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {s t : Set X} (hts : t ⊆ s) (hs : μ s ≠ ∞) (ht : μ t ≠ ∞)
    (hs0 : 0 < μ.real s) (ht0 : 0 < μ.real t) (f : SobolevSpace μ hQ)
    {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hvol : μ.real s ≤ C ^ 2 * μ.real t)
    (hfit : ‖normalizeLocalL2 μ s hs (SobolevSpace.restrictLp μ hQ s f)‖ ≤ E) :
    ‖normalizeLocalL2 μ t ht (SobolevSpace.restrictLp μ hQ t f)‖ ≤ C * E := by
  have hh := normalized_fit_restrict_sq μ hQ hts hs ht hs0 ht0 f (sq_nonneg E) hvol
    ((sq_le_sq₀ (norm_nonneg _) hE).mpr hfit)
  rw [← mul_pow] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hE)).mp hh

/-- On the half ball, the affine forcing is bounded by the original
residual norm and its Euler error. This supplies the coefficients needed
by radial transport without assuming their smallness. -/
theorem LocalHarmonicL2GradientInput.forcing_coefficients
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (f w η e : SobolevSpace (hausdorff n X) hX.quadratic) (B : ℝ), 0 ≤ B →
      ∀ hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R / 2)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ B ^ 2,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p (R / 2))] fun _ => (1 : ℝ)) →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n) (ell : Euclidean n) (k H V E : ℝ),
      0 ≤ H → 0 ≤ V → 0 ≤ E →
      (hausdorff n X).real (ball p R) ≤ V ^ 2 * (hausdorff n X).real (ball p (R / 2)) →
      (∀ c a, |c| + ‖N.symm a‖ ≤ H *
        ‖normalizeLocalL2 (hausdorff n X) (ball p (R / 2))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p (R / 2))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖) →
      (localRadialDerivative (hausdorff n X) hX.quadratic (ball p (R / 2)) f hf w =
        SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (R / 2))
          (w + sobolevColumnMap (hausdorff n X) hX.quadratic u ell + k • η + e)) →
      ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) e)‖ ≤ E →
      |k| + ‖N.symm ell‖ ≤ H *
        ((B * C / R + V) * ‖normalizeLocalL2 (hausdorff n X) (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ + V * E) := by
  obtain ⟨C, hC, hrad⟩ := hinput.radial_derivative_bound hn hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv f w η e B hB hf hw hη u N ell k H V E hH hV hE hvol hbound heuler he
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let α := ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp μ hQ (ball p R) w)‖
  have hs : ball p (R / 2) ⊆ ball p R := ball_subset_ball (by linarith)
  have hpos (r : ℝ) (hr : 0 < r) : 0 < μ.real (ball p r) :=
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport p r hr))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hrestrict (q : SobolevSpace μ hQ) (A : ℝ) (hA : 0 ≤ A)
      (hq : ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball p R) q)‖ ≤ A) :
      ‖normalizeLocalL2 μ (ball p (R / 2)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball p (R / 2)) q)‖ ≤ V * A :=
    normalized_fit_restrict_norm μ hQ hs _ _ (hpos R hR) (hpos (R / 2) (by linarith))
      q hV hA hvol hq
  have hD : ‖normalizeLocalL2 μ (ball p (R / 2))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (localRadialDerivative μ hQ (ball p (R / 2)) f hf w)‖ ≤ (B * C / R) * α := by
    exact hrad p R hR hcurv f w B hB hf hw
  exact projected_euler_coefficient_bound μ hQ (ball p (R / 2)) _ f w η e hf hη u N ell k hH
    hbound heuler hD (hrestrict w α (norm_nonneg _) le_rfl) (hrestrict e E hE he)

end RegularPointCoordinates

end

end OAI
