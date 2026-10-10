import OAI.Geometry.RCD.Harmonic.AffineEvaluation

namespace OAI

/-! # Consecutive actual affine fits and their center values -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- On a nested pair of fitting sets, the difference of the actual fits
is controlled by the two residuals, with the exact normalized volume loss. -/
theorem normalized_affineFit_difference (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (s t : Set X) (hts : t ⊆ s)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) (hs0 : μ s ≠ 0) (ht0 : μ t ≠ 0)
    (f : Lp ℝ 2 (μ.restrict s)) (c d : ℝ) (a b : Euclidean n)
    (hc : affineProjection μ hQ u s hs f = affineCoordinateMap μ hQ u s hs (c, a))
    (hd : affineProjection μ hQ u t ht (localL2Restriction μ s t hts f) =
      affineCoordinateMap μ hQ u t ht (d, b)) :
    ‖normalizeLocalL2 μ t ht (affineCoordinateMap μ hQ u t ht (c - d, a - b))‖ ≤
      (Real.sqrt (μ.real s) / Real.sqrt (μ.real t)) *
        ‖normalizeLocalL2 μ s hs (affineResidual μ hQ u s hs f)‖ +
      ‖normalizeLocalL2 μ t ht
        (affineResidual μ hQ u t ht (localL2Restriction μ s t hts f))‖ := by
  have heq : affineCoordinateMap μ hQ u t ht (c - d, a - b) =
      affineResidual μ hQ u t ht (localL2Restriction μ s t hts f) -
        localL2Restriction μ s t hts (affineResidual μ hQ u s hs f) := by
    change affineCoordinateMap μ hQ u t ht ((c, a) - (d, b)) = _
    rw [map_sub, ← hd, ← localL2Restriction_affine μ hQ u s t hts hs ht c a, ← hc]
    simp only [affineResidual, sub_apply, ContinuousLinearMap.id_apply,
      map_sub]
    abel
  rw [heq, normalizeLocalL2, smul_sub]
  have hn := norm_sub_le
    (normalizeLocalL2 μ t ht (affineResidual μ hQ u t ht (localL2Restriction μ s t hts f)))
    (normalizeLocalL2 μ t ht (localL2Restriction μ s t hts (affineResidual μ hQ u s hs f)))
  have hr := normalized_localL2Restriction_le μ s t hts hs ht hs0 ht0
    (affineResidual μ hQ u s hs f)
  exact hn.trans (by linarith)

variable [BorelSpace X] [ProperSpace X]

/-- Mean-value evaluation removes the constant term quantitatively from
consecutive least-squares fits. The coefficients need not be unique. -/
theorem affineFit_center_difference {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r R : ℝ) (_hr : 0 < r) (hrR : r ≤ R), -κ ≤ K * r ^ 2 →
    ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      (∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) (u i)) →
      ContinuousOn v (ball p r) →
      (∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
        (hausdorff n X).restrict (ball p r)] fun x => v x i) →
    ∀ η : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p r)] fun _ => (1 : ℝ)) →
    let μ := hausdorff n X
    let hs := ne_of_lt (hX.finiteOnBounded (ball p R) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let hsub := ball_subset_ball (α := X) (x := p) hrR
    ∀ (f : Lp ℝ 2 (μ.restrict (ball p R))) (c d : ℝ) (a b : Euclidean n),
      affineProjection μ hX.quadratic u (ball p R) hs f =
        affineCoordinateMap μ hX.quadratic u (ball p R) hs (c, a) →
      affineProjection μ hX.quadratic u (ball p r) ht
        (localL2Restriction μ (ball p R) (ball p r) hsub f) =
        affineCoordinateMap μ hX.quadratic u (ball p r) ht (d, b) →
      |(c + ⟪v p, a⟫_ℝ) - (d + ⟪v p, b⟫_ℝ)| ≤
        C * (Real.sqrt (μ.real (ball p R)) / Real.sqrt (μ.real (ball p r))) *
          ‖normalizeLocalL2 μ (ball p R) hs (affineResidual μ hX.quadratic u (ball p R) hs f)‖ +
        C * ‖normalizeLocalL2 μ (ball p r) ht
          (affineResidual μ hX.quadratic u (ball p r) ht
            (localL2Restriction μ (ball p R) (ball p r) hsub f))‖ := by
  obtain ⟨C, hC, heval⟩ := affine_evaluation_of_mean_value hX hmean hn hκ
  refine ⟨C, hC, ?_⟩
  intro p r R hr hrR hcurv u v hu hv hrep η hη μ hs ht hsub f c d a b hc hd
  have hb := heval p r hr hcurv u v hu hv hrep η hη (c - d) (a - b)
  have hfit := normalized_affineFit_difference μ hX.quadratic u (ball p R) (ball p r)
    hsub hs ht (ne_of_gt (hX.fullSupport p R (hr.trans_le hrR)))
    (ne_of_gt (hX.fullSupport p r hr)) f c d a b hc hd
  have hm := mul_le_mul_of_nonneg_left hfit (by linarith : 0 ≤ C)
  have he : c - d + ⟪v p, a - b⟫_ℝ = (c + ⟪v p, a⟫_ℝ) - (d + ⟪v p, b⟫_ℝ) := by
    rw [inner_sub_right]
    ring
  rw [he] at hb
  exact hb.trans (by nlinarith [hm])

end RegularPointCoordinates

end

end OAI
