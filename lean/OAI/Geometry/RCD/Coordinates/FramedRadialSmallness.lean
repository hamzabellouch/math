import OAI.Geometry.RCD.Coordinates.CenteredSplitting
import OAI.Geometry.RCD.Coordinates.CovectorRadialSmallness

namespace OAI

/-! # Qualitative radial error in the original coordinate frame -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Normalizing and centering are used only to estimate the error. The
result is the actual affine-fit error for the original map and covector. -/
theorem DyadicDistanceReplacements.framed_covector_fit_smallness
    {n : ℕ} {κ r0 B J C : ℝ} {p : X} {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {ε Cχ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ)
    (u : Fin n → SobolevSpace μ hQ) (A : Euclidean n ≃L[ℝ] Euclidean n)
    (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * (distanceSourceRadius r0 i / 64)) ε
      (transformedColumn μ hQ u A) v)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 ε
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v x - v p)))
    (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict (ball p (4 * (distanceSourceRadius r0 i / 64)))]
      fun _ => (1 : ℝ))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < μ.real (ball p (4 * (distanceSourceRadius r0 i / 64))))
    (b : Euclidean n) {L : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ L) :
    let r := distanceSourceRadius r0 i / 64
    let hfin : μ (ball p r) ≠ ∞ := ne_of_lt
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p r).measure_lt_top)
    (radialFitError μ hQ u p r hfin (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) ha) ^ 2 ≤
      ((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) * ε *
        (μ.real (ball p (4 * r)) / μ.real (ball p r)) * ‖A.symm b‖ ^ 2 := by
  dsimp only
  let r := distanceSourceRadius r0 i / 64
  let uA := transformedColumn μ hQ u A
  let uC := centeredColumn μ hQ uA (v p) η
  have hr : 0 < r := by
    have := distanceSourceRadius_pos S.radius_pos i
    dsimp only [r]
    positivity
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have hηr := ae_restrict_of_ae_restrict_of_subset hsub hη
  have hcenter := hfirst.center μ hQ (v p) η hη
  have hfin : μ (ball p r) ≠ ∞ := ne_of_lt
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p r).measure_lt_top)
  have haA := gamma_column_le_of_diagonal_bounds μ hQ uA (ball p r) (1 + ε)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hfirst.gradient j)) (A.symm b)
  have haC := gamma_column_le_of_diagonal_bounds μ hQ uC (ball p r) (1 + ε)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hcenter.gradient j)) (A.symm b)
  have hsmall := T.local_covector_fit_smallness μ hQ i hε hε1 hCχ uC
    (fun x => v x - v p) hcenter (by simp only [sub_self]) hmetric χ hvol (A.symm b)
  dsimp only at hsmall
  have hc := centeredColumn_radial_fit μ hQ uA p r hfin (v p) (A.symm b)
    η (T.distanceDatum μ hQ i) hηr haC haA
  have hf := radialFitError_frame μ hQ u p r hfin (T.distanceDatum μ hQ i) A b haA ha
  rw [hc, hf] at hsmall
  exact hsmall

end RegularPointCoordinates

end

end OAI
