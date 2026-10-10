import OAI.Geometry.RCD.Harmonic.LocalRadialSmallness
import OAI.Geometry.RCD.Coordinates.RadialFitSmallness

namespace OAI

/-! # Qualitative radial smallness in every constant covector -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The same actual radial smallness holds in every direction, with the
squared covector norm and only a dimensional loss. -/
theorem DyadicDistanceReplacements.local_covector_radial_error {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {ε Cχ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * (distanceSourceRadius r0 i / 64)) ε u v)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 ε
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • v x))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < μ.real (ball p (4 * (distanceSourceRadius r0 i / 64)))) (b : Euclidean n) :
    let r := distanceSourceRadius r0 i / 64
    (∫ x in ball p r, (localGamma μ hQ (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) x -
      SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u b) x) ^ 2 ∂μ) ≤
      (n : ℝ) * ((1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1)) * ε * r ^ 2 * μ.real (ball p (4 * r))) * ‖b‖ ^ 2 := by
  dsimp only
  let s := distanceSourceRadius r0 i
  let r := s / 64
  let q := T.distanceDatum μ hQ i
  have hr : 0 < r := by
    have := distanceSourceRadius_pos S.radius_pos i
    dsimp only [r, s]
    positivity
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have hgrad (j : Fin n) := ae_restrict_of_ae_restrict_of_subset hsub (hfirst.gradient j)
  have hh (j : Fin n) := (hfirst.harmonic j).mono μ hQ hsub
  have hm (j : Fin n) : MemLp (fun x => localGamma μ hQ q (u j) x -
      SobolevSpace.toLp μ hQ (u j) x) 2 (μ.restrict (ball p r)) :=
    (localGamma_memLp_two_of_bound μ hQ (ball p r) q (u j) (hgrad j)).sub
      ((Lp.memLp (SobolevSpace.toLp μ hQ (u j))).restrict _)
  exact (radial_linear_harmonic_correction μ hQ q u u hh hm
    (fun j => T.local_radial_error μ hQ i hε hε1 hCχ u v hfirst hv hmetric χ hvol j) b).2

/-- The actual dimensionless affine fit inherits the qualitative bound. -/
theorem DyadicDistanceReplacements.local_covector_fit_smallness {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {ε Cχ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * (distanceSourceRadius r0 i / 64)) ε u v)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 ε
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • v x))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < μ.real (ball p (4 * (distanceSourceRadius r0 i / 64)))) (b : Euclidean n) :
    let r := distanceSourceRadius r0 i / 64
    let hr : 0 < r := by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r]; positivity
    let hfin : μ (ball p r) ≠ ∞ := ne_of_lt
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p r).measure_lt_top)
    let hsub := ball_subset_ball (show r ≤ 4 * r by linarith)
    let ha := gamma_column_le_of_diagonal_bounds μ hQ u (ball p r) (1 + ε)
      (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hfirst.gradient j)) b
    (radialFitError μ hQ u p r hfin (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) ha) ^ 2 ≤
      ((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) * ε *
        (μ.real (ball p (4 * r)) / μ.real (ball p r)) * ‖b‖ ^ 2 := by
  dsimp only
  let r := distanceSourceRadius r0 i / 64
  have hr : 0 < r := by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r]; positivity
  have hfin : μ (ball p r) ≠ ∞ := ne_of_lt
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p r).measure_lt_top)
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have ha := gamma_column_le_of_diagonal_bounds μ hQ u (ball p r) (1 + ε)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hfirst.gradient j)) b
  have he := T.local_covector_radial_error μ hQ i hε hε1 hCχ u v hfirst hv hmetric χ hvol b
  have hf := radialFitError_sq_le_linear μ hQ u p r hfin (T.distanceDatum μ hQ i)
    (sobolevColumnMap μ hQ u b) ha b he
  apply hf.trans_eq
  calc
    _ = (((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) * ε *
        (μ.real (ball p (4 * r)) / μ.real (ball p r)) * ‖b‖ ^ 2) * (r ^ 2 / r ^ 2) := by ring
    _ = _ := by rw [div_self (pow_ne_zero 2 hr.ne'), mul_one]

end RegularPointCoordinates

end

end OAI
