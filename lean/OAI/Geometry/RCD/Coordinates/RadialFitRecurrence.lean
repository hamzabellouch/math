import OAI.Geometry.RCD.Coordinates.RadialFitCoordinates

namespace OAI

/-! # The dimensionless recurrence for actual least-squares radial fits -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)

/-- The harmonic correction gives a recurrence for the canonical actual
fit errors, with the exact contraction and restriction-volume factors. -/
theorem radialFitError_step_of_correction
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) (u i))
    (η : SobolevSpace (hausdorff n X) hX.quadratic)
    (hη : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) η)
    (hηone : SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) η =
      restrictedOne (hausdorff n X) (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)))
    (hfit : HasNormalizedAffineImprovement hX u p r θ)
    (q a h : SobolevSpace (hausdorff n X) hX.quadratic)
    {B E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
      localGamma (hausdorff n X) hX.quadratic a a x ≤ B)
    (hh : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) h)
    (herror : (∫ x in ball p r,
      (localGamma (hausdorff n X) hX.quadratic q a x -
        SobolevSpace.toLp (hausdorff n X) hX.quadratic h x) ^ 2 ∂hausdorff n X) ≤ E) :
    let μ := hausdorff n X
    let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
    let hsub := ball_subset_ball (mul_le_of_le_one_left hr.le hθ1)
    let hat := ae_restrict_of_ae_restrict_of_subset hsub ha
    let V := Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r)))
    radialFitError μ hX.quadratic u p (θ * r) ht q a hat ≤
      (V + (1 / 2 : ℝ) * θ * Real.sqrt θ) / (θ * r) *
        Real.sqrt ((μ.real (ball p r))⁻¹ * E) +
      (1 / 2 : ℝ) * Real.sqrt θ * radialFitError μ hX.quadratic u p r hs q a ha := by
  dsimp only
  let μ := hausdorff n X
  let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
  let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
  have hsub : ball p (θ * r) ⊆ ball p r := ball_subset_ball (mul_le_of_le_one_left hr.le hθ1)
  have hat := ae_restrict_of_ae_restrict_of_subset hsub ha
  have hstep := radial_fit_of_harmonic_correction hX u p hr hθ hθ1 hu η hη hηone hfit
    q a h hE ha hh herror
  change ‖normalizeLocalL2 μ (ball p (θ * r)) ht
      (affineResidual μ hX.quadratic u (ball p (θ * r)) ht
        (localL2Restriction μ (ball p r) (ball p (θ * r)) hsub
          (radialPairingLp μ hX.quadratic (ball p r) q a ha)))‖ ≤
    (Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r))) +
      (1 / 2 : ℝ) * θ * Real.sqrt θ) * Real.sqrt ((μ.real (ball p r))⁻¹ * E) +
    (1 / 2 : ℝ) * θ * Real.sqrt θ *
      ‖normalizeLocalL2 μ (ball p r) hs
        (affineResidual μ hX.quadratic u (ball p r) hs (radialPairingLp μ hX.quadratic (ball p r) q a ha))‖ at hstep
  rw [radialPairingLp_restrict μ hX.quadratic hsub q a ha hat] at hstep
  have hb := div_le_div_of_nonneg_right hstep (mul_pos hθ hr).le
  unfold radialFitError
  exact hb.trans_eq (by field_simp [hr.ne', hθ.ne']; ring)

end RegularPointCoordinates

end

end OAI
