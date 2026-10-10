import OAI.Geometry.RCD.Harmonic.HarmonicAffineImprovement
import OAI.Geometry.RCD.Coordinates.MeasuredCoordinateInput
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives

namespace OAI

/-! # Affine improvement in the original harmonic coordinate span

The measured compactness theorem is applied to normalized and recentered
coordinates. Invertibility and the local constant cutoff identify their
affine projection exactly with that of the original columns.
-/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem affine_improvement_from_metric_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hcompact : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n)
    (hmeasured : LocalMeasuredCoordinateInput hX) :
    ∃ m : ℕ, 3 ≤ m ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (p : X) (r : ℝ), 0 < r → -δ ≤ K * r ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        (∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
          (hausdorff n X).restrict (ball p r)] fun x => v x i) →
      ∀ (B : Euclidean n ≃L[ℝ] Euclidean n)
        (η : SobolevSpace (hausdorff n X) hX.quadratic),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
          (hausdorff n X).restrict (ball p r)] fun _ => (1 : ℝ)) →
        Measurable (fun x => (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
          (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) →
        IsPointedApproximation p 0 r 2 δ (fun x =>
          (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
          (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) →
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) w →
        ‖normalizeLocalL2 (hausdorff n X) (ball p r)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) w)‖ ≤ 1 →
        ‖normalizeLocalL2 (hausdorff n X) (ball p ((1 / 2 : ℝ) ^ m * r))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (affineResidual (hausdorff n X) hX.quadratic u
            (ball p ((1 / 2 : ℝ) ^ m * r)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
              (ball p ((1 / 2 : ℝ) ^ m * r)) w))‖ <
          (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m) := by
  obtain ⟨m, hm, happly⟩ := harmonic_affine_improvement_of_measured_approximation
    hX hn hcompact hgradient heuclidean
  obtain ⟨ε, hε, hεfit⟩ := happly 1 zero_lt_one
  obtain ⟨d, hd, hmeasure⟩ := hmeasured hn 1 ε zero_lt_one hε
  let δ := min d 1
  have hδ : 0 < δ := lt_min hd zero_lt_one
  refine ⟨m, hm, δ, hδ, min_le_right _ _, ?_⟩
  intro p r hr hcurv u v hrep B η hη hmeas happ w hw hnorm
  let μ := hausdorff n X
  let b : Euclidean n →L[ℝ] ℝ := -(innerSL ℝ ((B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)))
  let u' := affineChangedColumn μ hX.quadratic u B b η
  let f := fun x => (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
    (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)
  have hrep' (i : Fin n) : SobolevSpace.toLp μ hX.quadratic (u' i) =ᵐ[μ.restrict (ball p r)]
      fun x => f x i := by
    have hi := affineChangedColumn_representative μ hX.quadratic u (ball p r) v hrep B b η hη i
    have hb : b (EuclideanSpace.single i 1) =
        -((B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) i := by
      change -⟪(B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p), EuclideanSpace.single i 1⟫_ℝ = _
      simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
    filter_upwards [hi] with x hx
    change _ = ((B : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
      (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) i
    rw [PiLp.sub_apply]
    simpa only [hb, sub_eq_add_neg] using hx
  have hcurvd : -d ≤ K * r ^ 2 := (neg_le_neg (min_le_left d 1)).trans hcurv
  have hcurv1 : -1 ≤ K * r ^ 2 := (neg_le_neg (min_le_right d 1)).trans hcurv
  have hmeasured' := hmeasure p r hr hcurvd f hmeas
    (by simpa only [mul_one] using happ.mono_error (min_le_left d 1))
  let test : NormalizedHarmonicTest hX 1 ε := {
    center := p
    scale := r
    scale_pos := hr
    curvature := hcurv1
    coordinates := u'
    values := f
    target := w
    approximation := hmeasured'
    representative := fun i => by simpa only [one_mul] using hrep' i
    harmonic := by simpa only [one_mul] using hw
    normalized := by rw [one_mul]; exact hnorm }
  have hfit := hεfit test
  dsimp only [NormalizedHarmonicTest.residualNorm, test] at hfit
  rw [mul_one] at hfit
  have hsub : ball p ((1 / 2 : ℝ) ^ m * r) ⊆ ball p r :=
    ball_subset_ball (mul_le_of_le_one_left hr.le (pow_le_one₀ (by norm_num) (by norm_num)))
  have hη' := ae_restrict_of_ae_restrict_of_subset hsub hη
  have hηeq := restrictLp_eq_one_of_representative μ hX.quadratic η
    (ball p ((1 / 2 : ℝ) ^ m * r)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hη'
  have heq := affineChangedColumn_residual_eq μ hX.quadratic u B b η
    (ball p ((1 / 2 : ℝ) ^ m * r)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hηeq
  change ‖normalizeLocalL2 μ (ball p ((1 / 2 : ℝ) ^ m * r)) _
    (affineResidual μ hX.quadratic u' (ball p ((1 / 2 : ℝ) ^ m * r)) _
      (SobolevSpace.restrictLp μ hX.quadratic (ball p ((1 / 2 : ℝ) ^ m * r)) w))‖ < _ at hfit
  rw [heq] at hfit
  exact hfit

end RegularPointCoordinates

end

end OAI
