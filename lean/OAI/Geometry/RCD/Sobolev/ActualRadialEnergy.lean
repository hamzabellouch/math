import OAI.Geometry.RCD.Harmonic.ActualRadialPairing
import OAI.Geometry.RCD.Sobolev.RadialInteriorEnergy
import OAI.Geometry.RCD.Sobolev.PoissonAffineTransfer
import OAI.Geometry.RCD.Sobolev.RadialEnergyUnits
import OAI.Geometry.RCD.Coordinates.DyadicRadialFits

namespace OAI

/-! # Interior energy of the actual Poisson radial fits -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual Poisson radial derivative has an interior gradient fit
controlled by the distance value fit and the original Poisson defect.
The harmonic gradient constant is chosen before all centers and scales. -/
theorem actual_radial_fit_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX) (hgradient : LocalHarmonicL2GradientInput hX)
    (hn : 2 ≤ n) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧ ∀ {κ r0 B J C A ε Cχ : ℝ},
      0 ≤ κ → -κ ≤ K → 0 ≤ B → 0 ≤ J → 0 ≤ A → 0 ≤ ε → 0 ≤ Cχ →
      ∀ (p : X) (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
        (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C) (i : ℕ),
      distanceSourceRadius r0 i ≤ 1 → -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic),
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball p (distanceSourceRadius r0 i / 4)) (u j)) →
      ∀ hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
        localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + ε) ^ 2,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
        localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
          (A * distanceSourceRadius r0 i) ^ 2) →
      ∀ χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ,
      0 < (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) →
      2 * (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) ≤
        (hausdorff n X).real (ball p (2 * (distanceSourceRadius r0 i / 64))) →
      ∀ b : Euclidean n,
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let r := s / 64
      let hcoord := gamma_column_le_of_diagonal_bounds μ hX.quadratic u (ball p r) (1 + ε)
        (fun j => ae_restrict_of_ae_restrict_of_subset
          (ball_subset_ball (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; linarith : r ≤ s / 4))
          (hgrad j)) b
      ∃ G : LocalHessianPairing μ hX.quadratic (ball p r) (T.replacement i)
        (sobolevColumnMap μ hX.quadratic u b),
      ∀ (F : SobolevSpace μ hX.quadratic) {I : ℝ},
      IsSobolevHarmonicOn μ hX.quadratic (ball p r) F →
      ‖radialPairingLp μ hX.quadratic (ball p r) (T.distanceDatum μ hX.quadratic i)
        (sobolevColumnMap μ hX.quadratic u b) hcoord - SobolevSpace.restrictLp μ hX.quadratic (ball p r) F‖ ^ 2 ≤ I →
      (∫ x in ball p (r / 2), localGamma μ hX.quadratic (G.mixed - F) (G.mixed - F) x ∂μ) ≤
        radialEnergyConstant K n Cg ε A B J Cχ *
          (I / r ^ 2 + (s ^ (n : ℝ) * normalizedPoissonDefect μ hX.quadratic S i) * ‖b‖ ^ 2) := by
  obtain ⟨Cg, hCg, henergy⟩ := radial_interior_energy_from_fit hX hgradient hn hκ₀
  refine ⟨Cg, hCg, ?_⟩
  intro κ r0 B J C A ε Cχ hκ hK hB hJ hA hε hCχ p S T i hs1 hcurv u hu hgrad hf χ hvol hdouble b
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  let r := s / 64
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := div_pos hs (by norm_num)
  have hsub : ball p r ⊆ ball p (s / 4) := ball_subset_ball (by dsimp only [r]; linarith)
  have hcoord := gamma_column_le_of_diagonal_bounds μ hQ u (ball p r) (1 + ε)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hgrad j)) b
  obtain ⟨L, hL, hpairs⟩ := actual_distance_radial_pairing hX hhessian hκ hK hA hε hCχ
    p S T i u hu hgrad hf χ
  obtain ⟨G, hbound⟩ := hpairs b
  refine ⟨G, ?_⟩
  intro F I hF hfit
  let q := T.distanceDatum μ hQ i
  let D := (L : ℝ) ^ 2 * ‖b‖ ^ 2 *
    (4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) + κ * A ^ 2 * s ^ 2 * μ.real (ball p s))
  let P := annularPoincareConstant K n * r ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hP : 0 ≤ P := mul_nonneg (annularPoincareConstant_pos K n).le (sq_nonneg _)
  have hpoin := hX.annular_dirichlet_poincare hn p hr (by dsimp only [r]; change s ≤ 1 at hs1; linarith)
    hvol hdouble
  have hlap := T.laplacian_on_ball μ hQ i p (by rw [dist_self]; dsimp only [r]; linarith : r + dist p p ≤ s)
  have hu' := (IsSobolevHarmonicOn.linearCombination μ hQ hu b).mono μ hQ hsub
  have herr := T.local_energy_error μ hQ i (ball p r)
  have hvalue := G.fit_value_transfer μ hQ q F
    (mul_nonneg (sq_nonneg _) (sq_nonneg ‖b‖)) hcoord herr hfit
  have hb := henergy p r hr hcurv (T.replacement i) (sobolevColumnMap μ hQ u b) G
    hlap hu' hP hD hpoin 1 (by simpa only [one_mul] using hbound) F hF hvalue
  have hI : 0 ≤ I := (sq_nonneg _).trans hfit
  rw [normalizedPoissonDefect_units]
  exact radial_energy_natural_units hs hs1 hκ measureReal_nonneg measureReal_nonneg
    hB hJ hA hε hCχ hI hL hb

end RegularPointCoordinates

end

end OAI
