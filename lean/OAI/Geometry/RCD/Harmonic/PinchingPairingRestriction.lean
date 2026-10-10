import OAI.Geometry.RCD.Coordinates.RegularPinchingFrame
import OAI.Geometry.RCD.Sobolev.PoissonSpanLinearLift
import OAI.Geometry.RCD.Coordinates.RadialFitRestriction
import OAI.Geometry.RCD.Coordinates.CenteredNormalization

namespace OAI

/-! # The actual direction pairings in the small mass-test frame -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Removing the local constant does not change the exact frame used by
full-mass pinching. Both frame changes act on the original coordinate map. -/
theorem uncentered_frame_normalization {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (eta : SobolevSpace μ hQ) (z : Euclidean n)
    (F N : Euclidean n ≃L[ℝ] Euclidean n) (Ω : Set X) (hΩ : MeasurableSet Ω)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hN : IsExactMeanNormalization μ hQ
      ((centeredSobolevMap μ hQ u eta z).comp F.toContinuousLinearMap) Ω hΩ N) :
    sobolevMeanGram μ hQ ((sobolevColumnMap μ hQ u).comp
      (F.toContinuousLinearMap.comp N.toContinuousLinearMap)) Ω hΩ =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
  have hU := centered_transformed_columnMap μ hQ u F eta z
  rw [← hU] at hN
  unfold IsExactMeanNormalization at hN
  rw [sobolevMeanGram_comp, centeredColumn_meanGram μ hQ _ Ω hΩ _ eta heta,
    ← sobolevMeanGram_comp, sobolevColumnMap_transformed] at hN
  simpa only [ContinuousLinearMap.comp_assoc] using hN

omit [BorelSpace X] [ProperSpace X] in
/-- Restriction and a bounded exact frame preserve the actual constant
pairing, with only the square root of the volume loss. -/
theorem pinching_pairing_restrict {n : ℕ} {Ω Ω' : Set X} (hsub : Ω' ⊆ Ω)
    (hfin : μ Ω ≠ ∞) (hfin' : μ Ω' ≠ ∞)
    (hpos : 0 < μ.real Ω) (hpos' : 0 < μ.real Ω')
    (eta : SobolevSpace μ hQ)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω'] fun _ => (1 : ℝ))
    (G : Euclidean n →L[ℝ] SobolevSpace μ hQ) (delta : Euclidean n)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (hN : ‖N.toContinuousLinearMap‖ ≤ 2)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hvol : μ.real Ω ≤ C * μ.real Ω')
    (hfit : ∀ b, ‖normalizeLocalL2 μ Ω hfin
      (SobolevSpace.restrictLp μ hQ Ω (G b - ⟪delta, b⟫_ℝ • eta))‖ ≤ D * ‖b‖) :
    ∀ b, ‖normalizeLocalL2 μ Ω' hfin'
      (SobolevSpace.restrictLp μ hQ Ω' ((G.comp N.toContinuousLinearMap) b) -
        ⟪N.toContinuousLinearMap.adjoint delta, b⟫_ℝ • restrictedOne μ Ω' hfin')‖ ≤
      (2 * Real.sqrt C * D) * ‖b‖ := by
  intro b
  have hnorm : ‖N b‖ ≤ 2 * ‖b‖ :=
    (N.toContinuousLinearMap.le_opNorm b).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg b))
  have hbound := (hfit (N b)).trans (mul_le_mul_of_nonneg_left hnorm hD)
  have hbound2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ D * (2 * ‖b‖))).mpr hbound
  have hsmall := normalized_fit_restrict_sq μ hQ hsub hfin hfin' hpos hpos'
    (G (N b) - ⟪delta, N b⟫_ℝ • eta) (sq_nonneg (D * (2 * ‖b‖))) hvol hbound2
  have hsmall' : ‖normalizeLocalL2 μ Ω' hfin'
      (SobolevSpace.restrictLp μ hQ Ω' (G (N b) - ⟪delta, N b⟫_ℝ • eta))‖ ≤
      (2 * Real.sqrt C * D) * ‖b‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    apply hsmall.trans_eq
    simp only [mul_pow, Real.sq_sqrt hC]
    ring
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ← restrictLp_eq_one_of_representative μ hQ eta Ω' hfin' heta,
    ← map_smul, ← map_sub]
  exact hsmall'

end RegularPointCoordinates

end

end OAI
