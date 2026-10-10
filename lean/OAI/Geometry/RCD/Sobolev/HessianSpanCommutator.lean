import OAI.Geometry.RCD.Sobolev.HessianActionInput
import OAI.Geometry.RCD.Sobolev.HessianCommutatorEnergy

namespace OAI

/-! # The finite Poisson-span commutator with the original Bochner masses -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The Hessian action estimate yields the actual commutator
error and keeps the full shifted and ordinary Bochner masses explicit. -/
theorem LocalPoissonHessianActionInput.span_commutator_directional
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalPoissonHessianActionInput hX)
    {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (p : X) (r : ℝ) (hr : 0 < r) (L : ℝ≥0)
    (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
      (ball p (8 * r)) (U v) (ell v))
    (hgrad : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) :
    ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
      (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) ∧
      ShiftedBochnerLowerBound M ((hausdorff n X).restrict (ball p (2 * r))) ell n ∧
      ∀ t : ℝ, 0 < t → t ≤ 2 * r →
        ∃ G : ∀ v w, LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) (U v) (U w),
        ∀ v w z (Cv Cw Cz : ℝ), 0 ≤ Cv → 0 ≤ Cw → 0 ≤ Cz →
          (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
            localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ Cv ^ 2) →
          (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
            localGamma (hausdorff n X) hX.quadratic (U w) (U w) x ≤ Cw ^ 2) →
          (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
            localGamma (hausdorff n X) hX.quadratic (U z) (U z) x ≤ Cz ^ 2) →
          (∫ x in ball p t,
            (localGamma (hausdorff n X) hX.quadratic (U w) (G v z).mixed x -
              localGamma (hausdorff n X) hX.quadratic (U v) (G w z).mixed x -
              localGamma (hausdorff n X) hX.quadratic (U w) (U z) x) ^ 2 ∂hausdorff n X) ≤
            2 * ((Cw ^ 2 * Cz ^ 2) *
              ((M.measure v).real (ball p t) -
                (2 * ell v - (n : ℝ)) * (hausdorff n X).real (ball p t))) +
            2 * ((Cv ^ 2 * Cz ^ 2) * (M.measure w).real (ball p t)) := by
  obtain ⟨M, hM, hshift, hpairs⟩ := hinput κ hκ hK p r hr L U ell hU hgrad
  refine ⟨M, hM, hshift, ?_⟩
  intro t ht htr
  obtain ⟨G, hG⟩ := hpairs t ht htr
  refine ⟨G, ?_⟩
  intro v w z Cv Cw Cz hCv hCw hCz hv hw hz
  obtain ⟨hF, hDF⟩ := hG v w z 1
  obtain ⟨hV, hDV⟩ := hG w v z 0
  specialize hDF Cw Cz hCw hCz hw hz
  specialize hDV Cv Cz hCv hCz hv hz
  simp only [one_mul, one_pow, mul_one] at hF hDF
  simp only [zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hV hDV
  exact local_hessian_commutator_energy (hausdorff n X) hX.quadratic
    (G v w) (G w v) (G v z) (G w z) hF hV hDF hDV

/-- The uniform span bound follows by using its common gradient constant. -/
theorem LocalPoissonHessianActionInput.span_commutator
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalPoissonHessianActionInput hX)
    {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (p : X) (r : ℝ) (hr : 0 < r) (L : ℝ≥0)
    (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
      (ball p (8 * r)) (U v) (ell v))
    (hgrad : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) :
    ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
      (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) ∧
      ShiftedBochnerLowerBound M ((hausdorff n X).restrict (ball p (2 * r))) ell n ∧
      ∀ t : ℝ, 0 < t → t ≤ 2 * r →
        ∃ G : ∀ v w, LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) (U v) (U w),
        ∀ v w z,
          (∫ x in ball p t,
            (localGamma (hausdorff n X) hX.quadratic (U w) (G v z).mixed x -
              localGamma (hausdorff n X) hX.quadratic (U v) (G w z).mixed x -
              localGamma (hausdorff n X) hX.quadratic (U w) (U z) x) ^ 2 ∂hausdorff n X) ≤
            2 * (((L : ℝ) ^ 4 * ‖w‖ ^ 2 * ‖z‖ ^ 2) *
              ((M.measure v).real (ball p t) -
                (2 * ell v - (n : ℝ)) * (hausdorff n X).real (ball p t))) +
            2 * (((L : ℝ) ^ 4 * ‖v‖ ^ 2 * ‖z‖ ^ 2) * (M.measure w).real (ball p t)) := by
  obtain ⟨M, hM, hshift, hpairs⟩ := hinput.span_commutator_directional hκ hK p r hr L U ell hU hgrad
  refine ⟨M, hM, hshift, ?_⟩
  intro t ht htr
  obtain ⟨G, hG⟩ := hpairs t ht htr
  refine ⟨G, ?_⟩
  intro v w z
  have hbound (a : Euclidean (n + 2)) :
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
        localGamma (hausdorff n X) hX.quadratic (U a) (U a) x ≤ ((L : ℝ) * ‖a‖) ^ 2 := by
    have hh := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show t ≤ 8 * r by linarith)) (hgrad a)
    simpa only [mul_pow] using hh
  have he := hG v w z ((L : ℝ) * ‖v‖) ((L : ℝ) * ‖w‖) ((L : ℝ) * ‖z‖)
    (by positivity) (by positivity) (by positivity) (hbound v) (hbound w) (hbound z)
  convert he using 1; ring

end RegularPointCoordinates

end

end OAI
